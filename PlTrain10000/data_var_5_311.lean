variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233038307067837873964401228412 : ((p4 ∧ (p5 ∧ p4)) → (((p5 → (((p2 → (((False → (p4 ∧ (p3 ∧ True))) ∧ p5) → p3)) → p4) → (p1 ∧ (p2 ∧ p2)))) ∧ p2) ∨ p5)) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174897342221566927358454373408 : (((p3 ∧ p2) → (p1 ∧ ((p1 ∧ p4) → ((True → (p3 → p5)) ∧ (True ∧ p2))))) → ((p1 ∨ p3) ∨ ((p5 ∨ (p5 ∧ p4)) ∨ (p1 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39622854202305271398353278125 : (((p2 ∨ (p3 ∨ ((p5 ∨ ((False ∧ p5) ∧ ((False ∧ ((p4 → p1) ∨ p1)) ∨ (((p5 ∧ p5) → (p2 ∧ p1)) ∧ p5)))) ∧ True))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346363555717164643134614234065 : (p3 → (((p3 ∨ p5) → (((True ∧ ((((p5 ∧ p4) ∨ p4) ∧ p1) ∧ ((p3 → ((p5 ∧ p2) ∨ p3)) ∧ p4))) ∨ p3) ∨ p3)) ∨ (p1 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616718190555931865685627927941 : (((((((False → p5) ∨ (True ∨ (p4 → (False → True)))) → p1) ∨ (((p5 → p2) ∨ (((p5 → p4) ∧ (True ∧ p4)) → p4)) ∧ p2)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133766491577289406628672094070 : ((((p4 ∨ (p1 ∨ ((p1 ∧ False) ∧ p5))) → ((((p5 ∨ p1) ∧ (p1 ∨ (p3 → (p2 ∧ True)))) ∧ False) ∧ p3)) ∧ False) ∨ ((p1 ∧ p1) → p1)) := by
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
theorem thm_5_vars_328729378954575101161293780292 : (True → (((p4 → ((p2 → p3) ∨ (p3 ∨ (p2 ∨ (p1 ∨ True))))) → True) → ((((p3 → ((p3 → p4) ∨ (p1 ∧ p1))) → False) ∨ p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350007924391288035922227165994 : (p4 → (((p2 ∨ ((False ∨ p1) ∧ ((p4 → True) ∧ (False ∧ ((((p5 → ((False ∧ p3) ∨ p5)) ∧ (p2 ∧ True)) ∧ p5) ∧ p3))))) ∨ p4) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766776070543297166327294115034 : (((p4 ∧ (p2 ∨ (p4 ∧ ((((p3 ∧ (((True → p1) ∨ p2) ∨ (p4 → True))) → (False ∧ True)) → ((p1 ∧ p1) ∧ False)) ∧ (p5 ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164995090012797847246176204786 : (((((((p2 ∨ p1) ∨ p4) → (p4 → p1)) → p2) ∧ ((p5 → (True ∨ p3)) ∧ True)) → p4) ∨ (p5 → ((p5 ∧ ((False ∧ True) → p3)) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149254912461951514584623544811 : (((p3 ∨ p1) ∨ (((((p5 → True) ∨ (False ∧ ((True ∨ (p2 ∧ p2)) → p1))) → p5) ∧ (True ∧ True)) → p3)) ∨ ((p2 ∧ False) → (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226863313103167336586431539525 : (((p5 ∧ True) → p3) ∨ ((((((p2 ∧ (p3 ∧ False)) ∨ ((p5 ∨ (p5 ∨ p5)) ∧ (p1 ∧ True))) ∨ ((False ∨ True) ∨ p2)) ∨ p5) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179315843105243124524415478928 : ((False ∨ (False ∨ (((p5 ∨ (p1 ∨ p2)) ∧ ((False → True) ∨ False)) → p2))) ∨ (p4 → (((((p1 ∨ p1) ∧ p5) ∧ True) ∧ (p3 ∨ p2)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119060699944611047594930176911 : ((p1 → ((((p2 ∧ p2) → (p4 ∨ (True ∨ p4))) ∨ ((((False ∧ (p1 ∨ False)) ∧ (p2 ∨ p1)) ∧ (False ∨ p3)) → p3)) → p4)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156608097811757239497438768489 : (((((False ∨ False) ∨ (p2 → (False ∧ ((((p2 ∨ (p1 → p3)) ∧ p4) ∧ False) ∨ p2)))) ∧ p1) ∧ p1) ∨ (p1 → (p3 → (True → (True ∧ p1))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62509126565457603632385912659 : ((p3 ∧ (p2 ∧ (p2 ∨ ((((p3 → ((True ∧ (p4 → (p2 ∧ p5))) → (p2 ∨ (False → (False → p2))))) ∨ p2) → (p1 ∨ p3)) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249555250155308659387930182824 : ((p5 ∨ p2) ∨ ((((((True ∧ p5) ∨ p1) ∧ (False ∨ (p4 → p1))) ∨ p3) ∨ p1) ∨ ((p1 ∧ False) → ((False ∧ p5) ∧ ((p4 ∧ False) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342106451625506868124523334338 : (p2 → (((((p1 ∧ ((p4 ∧ p2) ∧ (p5 ∨ ((p2 ∧ p5) ∨ p4)))) ∧ p1) ∨ (True → p5)) ∨ (p3 → p2)) ∧ (p2 ∨ ((p5 → p1) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148482801601798478695414915235 : (((((p5 ∧ p5) ∧ (p2 ∧ ((p4 ∨ p2) ∧ (p3 → True)))) ∨ True) ∨ ((((True ∧ p2) ∨ True) ∨ p5) ∨ p3)) ∨ (((True → p1) ∧ p4) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147865164964710485786168364494 : (((p2 → ((((False ∨ (p5 ∨ False)) ∧ (((p4 ∧ (True ∧ False)) ∨ p3) ∧ (True → p5))) → p5) → p4)) → False) ∨ (((p3 ∧ p3) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618117104190961267585016742334 : (((((p3 ∧ ((p1 ∨ p3) ∧ True)) ∧ ((p5 → p4) ∨ ((p5 → (p4 → False)) ∨ (p2 ∧ ((p1 ∧ (p2 ∨ (p1 ∧ p1))) ∨ p5))))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_118102518449389712684881033782 : ((False ∨ (((((((((True → p2) → True) ∧ ((p4 ∨ p5) → p4)) → p3) → p1) ∨ p2) ∧ (False ∧ True)) ∨ (p4 ∧ False)) ∨ True)) ∨ (p1 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53246719879097340834284824226 : ((((p1 ∧ p2) ∧ ((True → p5) ∨ (p5 ∧ ((p2 ∧ True) ∧ p4)))) ∨ (False ∨ ((False → p2) ∨ ((p2 ∧ ((p3 ∧ p1) ∨ p3)) ∨ p1)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_709840240731702953919107855465 : ((((p4 → ((p5 → (p3 → (True → False))) → p3)) → (p5 ∨ ((False ∨ (True → p5)) → (True → ((((p1 ∨ p3) → True) ∨ p1) ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38939981118022725003608192218 : (((((False → p3) → p3) → (((p2 ∧ True) → True) → ((p3 → (False → p1)) → (p4 → (p2 ∧ (((False → p2) ∨ p1) ∨ p3)))))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116366347221540156490884660918 : ((((p3 ∧ p1) → p5) → ((p4 ∨ ((p2 ∧ p1) ∨ ((True ∨ False) ∨ p5))) ∧ ((False ∧ (p4 ∨ (p3 ∨ (p1 ∨ True)))) ∧ p2))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260526821785928910944873430891 : ((p3 → p1) → (((p5 → (p3 → p3)) ∧ (p4 ∧ (((((p4 ∨ (True ∧ p5)) ∨ (p2 ∨ p3)) ∨ p5) ∧ True) ∨ ((p1 ∧ p3) ∧ p1)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116343031378824073927846496586 : ((((p1 ∧ p5) ∨ p4) → (((((((p1 → (p4 ∨ p2)) ∨ ((False ∧ p1) → p2)) ∨ (p3 ∨ True)) ∧ p1) ∨ p1) ∧ p1) ∨ p4)) ∨ (p4 ∧ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_974345987931310498184687533877 : ((((False → p2) → (True ∧ ((p5 ∧ ((((True ∨ p1) ∨ (p2 ∨ (p5 ∧ (p4 → (True ∨ p5))))) → False) ∨ (p5 → (p2 ∨ True)))) ∧ False))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68136847946806546314105801870 : ((p3 → (((((p2 → (p5 → (((True ∧ p2) ∨ p5) ∨ ((True ∨ (p1 ∨ p1)) ∧ (False → p5))))) ∧ p3) → (p5 ∧ p4)) ∨ True) ∧ p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111166749361729571167263083554 : ((((False ∧ ((p2 ∧ p2) ∧ p4)) ∧ (((p4 ∧ p1) ∧ p4) ∨ (p3 ∧ (p5 ∨ (p2 → (True ∨ ((True ∧ True) → False))))))) ∧ p3) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_24888586519897463151952021824 : ((((p4 ∧ p4) → p1) ∨ (p3 → (p5 ∨ (((p2 ∧ (p5 ∧ (False ∨ p3))) ∧ (p1 ∨ (p1 → ((False ∧ True) ∧ (p5 ∨ p3))))) ∨ True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309388774281459461734740654127 : (p2 ∨ ((p4 ∧ ((((p4 → (p3 ∨ (p4 → (True ∧ p4)))) ∨ p2) ∨ (((p4 → True) ∧ ((p5 → False) → p3)) → p2)) → p4)) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114962447384939925091661871510 : (((p4 ∨ ((p3 ∨ p3) ∧ ((p1 → True) ∨ ((p4 ∧ True) → (p1 ∧ p3))))) → (p4 ∧ (p1 ∧ ((p2 ∨ p4) ∨ (p5 → False))))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62302576355265509352274216220 : ((p3 ∧ (((((p2 ∨ ((p1 ∨ True) → (p3 → (p1 → p2)))) ∨ True) ∧ ((p3 ∨ p5) ∨ p1)) ∧ (True ∨ (False ∨ p4))) ∧ (False → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617300124972780442275433648759 : ((((((p4 → ((p5 → (p2 ∨ False)) → True)) ∧ p2) → (True ∧ (((p1 ∧ p3) ∧ (((p1 ∨ (True ∨ True)) → p5) → True)) ∧ True))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53552139595672964225777978775 : ((((p2 ∨ ((((True → p1) → p3) ∧ p2) ∧ True)) ∧ p5) ∧ ((p3 → True) → (p3 → ((False ∧ (False ∧ ((p3 ∨ p5) ∨ p4))) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148029776242795428574650580892 : (((((p3 ∨ p1) → p3) ∧ ((True → p1) ∧ (False ∨ ((p1 ∧ p2) ∨ ((p5 ∨ p2) → p2))))) ∨ (p4 → p4)) ∨ ((False → p2) ∨ (p1 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248242683590234000550332259094 : ((p2 ∨ p1) ∨ (p3 ∨ (((True → p3) ∨ (p1 → (p4 ∨ (True ∨ (p5 → (p4 → (p3 ∨ (p2 → p4)))))))) → ((False ∨ p4) → (p5 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134432000014429254382056163476 : (((p5 → ((p4 ∧ ((p3 ∧ ((((False ∧ p1) → p1) ∧ (p2 ∨ p5)) → p5)) ∨ p2)) ∨ ((p4 → p5) ∧ p2))) ∨ True) ∨ (False ∨ (p5 ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249852119808889729656275238937 : ((True → False) ∨ (((p1 ∧ ((((p1 ∧ False) ∨ (((True ∧ p5) ∨ p5) → False)) → (p3 → p5)) → p5)) ∨ (False ∨ False)) ∨ (False → (True → False)))) := by
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
theorem thm_5_vars_745552300625664443977180241378 : ((((True ∨ p1) → (((True ∨ (p5 ∨ (p1 ∨ (p1 → (p3 → ((((False → (p3 → p5)) → (p4 → p1)) ∧ p5) ∧ True)))))) ∧ p4) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180379057558939784755676227958 : ((((p2 ∧ ((p2 ∨ p3) ∨ False)) ∨ ((p3 → False) → p5)) ∨ (False ∨ False)) → ((p5 ∨ ((p2 → (p5 ∧ False)) → ((p1 → p5) ∧ True))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
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
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50955612360970192095578238447 : ((((True ∧ ((p4 ∧ p5) → (p1 → p5))) ∧ ((((p3 → p4) → False) ∧ p4) → (p5 → p1))) ∧ (((p3 ∨ p3) ∨ p4) ∧ (False ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183970059518454811659615430536 : (((p3 → ((p1 ∨ (False ∨ p4)) → ((p3 ∨ False) ∨ p3))) ∧ p1) ∨ (((p4 ∨ False) ∨ p2) ∨ (p3 ∨ ((True ∨ ((p5 → p2) → p5)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_204327199897597918516670178895 : (((p3 ∧ (p1 ∨ (p5 ∧ p1))) ∧ p4) ∨ (p3 ∨ (p2 → ((p1 → (p5 → (p5 ∨ False))) ∨ ((False → (p1 → True)) ∨ ((p2 → True) ∧ p3)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165996405494379591851765731791 : (((p4 ∧ False) ∨ ((p5 ∧ (((True ∧ True) ∨ p1) ∧ (p1 ∨ ((False ∨ p5) ∧ p2)))) ∧ p1)) ∨ (((p5 → (p5 ∨ False)) ∧ (True → p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341735935915447925661208307979 : (p2 → (((p1 ∧ True) ∨ ((p5 ∧ ((p1 ∧ ((False ∧ p5) → ((p5 ∨ False) ∧ (p1 ∨ (p3 ∨ True))))) → False)) ∧ (p5 ∨ p3))) ∨ (p2 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54375847729983620492879984099 : (((p1 → (False ∨ ((True ∨ True) ∨ (p4 → False)))) ∧ (((((((p5 ∧ ((p2 ∨ p4) ∧ p3)) ∨ False) ∧ False) → p4) ∧ True) → p1) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60211877060630118994018327469 : (((True → False) → ((((False ∨ ((p1 ∧ (p1 ∧ p3)) ∨ p3)) ∨ p5) → (p4 ∨ (p5 ∨ ((True ∨ p5) ∧ (False ∧ True))))) ∨ (False → p5))) ∨ p3) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208782819272000204455997363601 : ((p2 ∧ ((p4 → p5) → (p5 ∧ False))) → (((True ∧ p2) ∧ (((False → p4) ∧ (((p4 ∨ p1) → p2) → (p5 ∧ (p4 ∨ p4)))) ∨ p2)) ∨ p2)) := by
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
theorem thm_5_vars_115359733480735621549330429176 : (((((p4 ∧ p2) ∧ (p3 ∨ (p1 → p5))) ∨ p4) ∧ ((False ∨ ((p4 ∨ False) → (p3 ∧ ((p2 → (p4 ∧ True)) → p4)))) ∧ False)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40380409716359781080018059305 : (((((False ∨ ((p4 ∨ p4) → (True → (True ∨ ((False ∧ p2) ∨ ((p2 ∧ (p2 ∧ (False ∧ False))) ∧ p2)))))) ∧ (p4 ∧ False)) ∨ p4) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127033234793843887051324634250 : ((False ∨ (((p3 ∧ (p4 → p3)) → (((((True → p3) ∧ (((p2 ∧ p3) → (True ∧ p2)) ∧ p4)) ∧ p3) → p5) → p4)) ∨ p5)) → (p5 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663161585830702459074791727608 : (((((True → p2) ∧ (((p4 ∧ (p1 ∧ p3)) → (((False → (p5 ∧ True)) ∧ False) ∨ ((p3 ∧ p5) → p3))) → (p1 ∧ p3))) → (p2 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38929478695650045431658018030 : (((((p5 ∧ p1) ∨ False) → ((p1 ∨ (p4 ∨ p5)) → (False ∨ (((True ∨ (True ∨ (p3 ∨ (p3 ∧ False)))) ∨ p1) ∧ (True ∧ p4))))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244187792175127909966400577664 : ((True ∧ p5) ∨ ((((((p1 ∨ p3) ∧ (((p4 ∨ p5) ∨ ((p1 ∨ (p3 ∧ p3)) → (p2 ∨ p2))) → p5)) ∨ True) ∨ (True → True)) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624844858612818021215867549377 : ((((p5 ∨ ((((p3 → ((p5 ∨ (((p2 ∨ p1) → p3) ∧ ((p1 ∧ p4) ∧ p5))) → p3)) → p3) ∨ p1) ∨ ((p4 ∨ True) → True))) ∨ p3) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_174814943490922475279354225015 : (((p4 → True) ∧ (((p1 ∧ (p3 → False)) ∧ True) ∨ (((p1 ∨ p1) ∧ p3) ∧ p2))) → ((False → p2) ∧ ((False ∨ p1) ∧ (p4 ∨ (False → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h24
    -- False on the left can always be used.
    apply False.elim h24
  case inr h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- Conjunctions on the left can always be decomposed.
    let h28 := h26.left
    let h29 := h26.right
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h30 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h31
      -- False on the left can always be used.
      apply False.elim h31
    case inr h32 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h33
      -- False on the left can always be used.
      apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731642332693030101418271199304 : ((((p1 → (p2 → False)) → (((p1 ∧ ((p3 → p2) ∧ (p2 ∧ True))) ∨ True) ∧ ((((p4 → ((p5 → p4) → p5)) ∨ p4) ∧ p5) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147989297275604142786554764759 : (((((((p4 → p5) ∨ p3) ∨ p5) ∨ (((p3 → ((p4 → p1) ∧ p5)) ∨ p3) → p4)) ∨ False) ∨ (p2 ∧ False)) ∨ (p3 ∨ ((True → p1) → p1))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190911955041541574113850280761 : (((p4 → (((p3 ∧ p5) ∨ p1) ∧ p3)) → (p5 ∨ p5)) ∨ (p2 → (False ∨ ((False → p5) ∨ ((p4 → p5) ∨ (True ∧ ((p5 ∧ p2) ∨ False))))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326100487574254327668852990191 : (p5 ∨ (p1 → ((p1 ∧ (((p4 ∧ (((False → True) → False) ∨ p4)) ∧ ((((True → False) ∨ False) → (p2 ∨ p4)) → p3)) ∨ (p3 ∨ True))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193937101932164672224601115915 : ((p2 ∨ (((p2 ∨ (False ∨ (True → p2))) ∧ p5) ∨ False)) → ((False ∨ p3) ∨ ((False → ((p5 ∧ p5) ∨ ((p5 ∧ True) ∨ p2))) ∧ (False → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h10
        -- False on the left can always be used.
        apply False.elim h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h15
          -- False on the left can always be used.
          apply False.elim h15
          -- Implications on the right can always be decomposed.
          intro h16
          -- False on the left can always be used.
          apply False.elim h16
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46183406008583351477727198749 : ((((True ∧ ((p3 ∧ (p1 → (True ∧ p2))) ∧ (((p1 ∧ (p2 ∨ False)) → p4) ∧ (((p2 ∨ False) ∨ p4) ∧ p4)))) → p5) ∧ (p2 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111569328061345867428364632469 : ((((((p2 → p5) ∧ True) ∨ (((True ∧ p4) ∨ p1) ∨ (p3 ∧ (p2 → ((False ∧ (p1 ∨ p4)) ∨ (p1 ∨ p3)))))) ∧ True) ∨ True) ∨ (p1 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245220363825228794799708234787 : ((p2 ∧ p1) ∨ ((((False ∨ (p1 ∨ False)) → (((((p2 ∨ (p2 → (p4 → p2))) → p2) ∧ p5) ∧ (p1 → p4)) ∨ (p3 → True))) ∨ False) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111997714995890670588889296351 : (((((p3 ∨ (False → p3)) ∧ False) ∨ ((p5 ∨ (((True → p2) ∧ False) → ((p3 → (True ∨ (p2 ∧ p3))) → True))) → p5)) ∨ True) ∨ (False ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342646215553314986597938016125 : (p2 → ((False → ((((True ∧ p5) ∧ (True ∨ p4)) ∧ p3) → p5)) ∧ ((p2 ∧ (((((p1 ∨ False) → (p4 ∨ False)) ∨ False) → p2) → False)) ∨ True))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42300333585626874389981102761 : (((p2 ∧ (((True ∧ (((False ∨ True) ∨ p1) ∧ ((p4 ∨ p5) ∨ ((p5 → True) ∧ True)))) ∧ ((True ∨ p5) → p1)) ∧ (p3 ∨ p5))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117468583787119004156593127853 : ((p1 ∧ (p1 ∧ ((p1 → (p5 → (p1 ∧ False))) → (((p1 ∧ (((p5 ∧ p2) ∧ p2) ∨ p3)) ∨ p1) ∧ ((True ∨ p1) → p1))))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657398560211668451071441134386 : (((((p2 → p3) ∧ ((p5 ∧ p5) ∨ (p3 ∨ (p1 ∧ ((p3 ∨ ((((p2 → False) → True) → p5) → p2)) → (True ∧ False)))))) ∨ (True → True)) ∨ p4) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315660081672682765499757621381 : (p3 ∨ ((p3 ∧ False) ∨ ((((((((p5 ∨ p3) ∧ p1) → p1) ∧ p4) ∧ (((p1 ∧ p1) ∧ True) → p1)) ∧ ((p5 ∨ p4) ∧ p3)) ∨ True) ∨ False))) := by
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
theorem thm_5_vars_50298722322928863545659497767 : ((((p5 ∧ ((True → p2) ∨ ((((p2 → True) ∨ (p2 ∨ False)) ∨ p5) → p5))) ∨ (True ∨ (p1 ∨ True))) ∨ (((p4 ∧ p5) → p2) ∧ p1)) ∨ p5) := by
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
theorem thm_5_vars_178272396633550545904329908257 : (((((p1 ∨ p2) ∨ p5) ∨ (((p4 → False) ∨ p3) ∨ p5)) ∧ (p1 → p5)) ∨ ((p1 ∧ p2) → (((p5 ∨ (False ∨ False)) ∨ p4) ∨ (p2 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205660828563804989328272912306 : (((False ∨ p4) ∨ (p5 ∧ (p1 ∧ True))) ∨ ((p3 → p2) ∨ ((p4 ∧ p5) ∨ (((((p3 ∧ p1) ∨ p3) ∨ False) ∧ (p3 ∨ p4)) ∨ (True ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_611289151219899904234956315766 : ((((((p4 ∨ False) ∨ (((p2 ∨ (((((False → p5) → p3) ∧ ((p2 → p2) → p3)) → p4) ∧ False)) ∨ p1) → (p2 ∧ p4))) → p5) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_46827094227389408324292013047 : ((((((p4 → p5) ∧ ((((p4 ∨ (p1 → p2)) → ((p1 ∧ False) ∨ (False ∨ p5))) ∨ True) ∨ p1)) → (p2 ∧ True)) ∧ False) ∨ (False → False)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324202512898552960879120408383 : (p5 ∨ ((((p1 → p1) ∧ p5) ∨ (p1 ∨ ((False ∨ p3) → p3))) → ((((((p2 ∧ p3) ∨ (p5 → p2)) → p1) ∧ p2) ∨ p5) ∨ (p5 → True)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103033756142914374082004053760 : (((((p5 → ((p2 → (True → p4)) ∧ p2)) → p4) → (((p2 ∨ p1) ∨ p3) ∨ ((p1 → (p3 ∧ p2)) ∨ (p5 ∧ p4)))) ∨ True) ∧ (p5 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_856219330126210016974655776226 : ((((((True ∧ ((True ∧ ((((False ∧ False) → p1) ∨ p5) → ((p2 ∧ p3) → p4))) ∧ p2)) ∨ ((p3 → (p1 ∧ p1)) ∨ True)) ∨ True) → p5) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True ∧ ((True ∧ ((((False ∧ False) → p1) ∨ p5) → ((p2 ∧ p3) → p4))) ∧ p2)) ∨ ((p3 → (p1 ∧ p1)) ∨ True)) ∨ True) := by
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
theorem thm_5_vars_145532229126205813515052491097 : ((((p1 ∧ p1) ∧ p4) ∨ (((((((True ∨ p4) → (False ∧ p4)) ∨ True) ∧ False) ∨ True) ∨ (p1 ∨ p5)) ∧ True)) ∧ (((p3 → p2) ∨ p2) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258910425449976286232979941841 : ((True → p2) → (((p1 ∨ False) ∧ (p1 ∨ ((p4 ∨ True) → False))) ∨ ((False ∧ (False ∧ ((p1 ∧ False) ∧ (p2 ∧ (p1 ∨ (p2 → p5)))))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328098186758844135547717121815 : (True → (((((((((p5 → p4) ∨ p3) → True) → p4) ∨ (((True ∧ p1) ∨ p2) ∧ p3)) ∧ True) ∨ (False ∨ p1)) ∨ False) ∨ ((p3 ∧ p4) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2310960383635651774199921706 : (((((p4 ∨ (False ∨ (p3 → p1))) ∧ p2) ∧ True) ∧ (p5 ∨ (p4 ∧ True))) → (p3 ∨ (((p3 → p4) → (p2 → False)) → (p3 ∨ True)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h23
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18968485827921948058129939053 : (((p1 → ((True → ((p5 ∧ (p3 ∧ True)) → p1)) ∧ ((p4 ∨ ((p1 → p1) ∨ p2)) → p5))) ∨ ((((p4 ∨ p5) → True) ∧ p4) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204265231393107798972797237606 : ((((p2 ∨ p3) ∨ (p2 ∨ p2)) ∧ p4) ∨ ((p5 ∧ False) → (((p5 ∨ p2) → ((True → (p3 ∨ p1)) ∧ ((p5 → (p3 ∧ p5)) ∨ p3))) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- False on the left can always be used.
    apply False.elim h9
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h1.left
    let h15 := h1.right
    -- False on the left can always be used.
    apply False.elim h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_862123904375887656745489642528 : ((((((p5 → (True → ((p1 → (p2 ∨ p5)) → p5))) → (((False ∨ p3) ∨ p2) ∧ (p5 ∧ p3))) ∨ (False → ((p5 → False) ∧ p3))) → p3) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 → (True → ((p1 → (p2 ∨ p5)) → p5))) → (((False ∨ p3) ∨ p2) ∧ (p5 ∧ p3))) ∨ (False → ((p5 → False) ∧ p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113202803146517307047730991974 : (((((((p1 ∧ p1) → p5) ∧ ((p4 → ((p4 ∨ p1) → (((p5 ∨ p5) ∨ p4) ∧ p5))) ∨ p4)) → p2) ∨ p3) ∧ (p1 → p2)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335702640370980730355956017570 : (p1 → ((((p5 ∧ ((False ∧ True) ∧ p2)) ∨ ((((p1 ∨ True) ∧ p1) → (p5 ∧ ((p3 ∧ False) ∨ (p3 ∨ p4)))) ∧ (False → p4))) ∨ True) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111422224231023336304976770413 : (((p3 ∨ (True → (((p5 ∨ p3) ∧ (((p1 ∨ (p1 ∧ p2)) → ((p5 → p3) ∨ p3)) ∨ (True ∨ (p4 ∨ p1)))) ∧ True))) ∧ p5) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586960343046040621906449623247 : (((((p3 ∨ ((((False ∧ p4) ∨ p3) ∧ ((p3 → p3) → (True ∧ (p4 → (False ∨ ((False ∧ (False ∨ False)) → p4)))))) ∨ p2)) ∧ False) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56207104130726297653235530050 : (((False ∨ (p2 ∧ (p1 ∨ False))) ∨ ((p5 ∨ (False → ((((p5 → p4) ∧ p1) ∨ p4) ∧ (False ∨ (((p1 ∨ p4) ∧ p3) ∧ p4))))) ∨ False)) ∨ p4) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172226490492483039547127354296 : (((p3 → (False → (p5 ∨ ((True ∨ p1) → (True → p4))))) → ((p1 ∨ p3) → p3)) ∨ (False → ((((p2 → True) ∨ p4) ∨ (p1 → p5)) ∧ p1))) := by
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
theorem thm_5_vars_326149961798343743145971924126 : (p5 ∨ (p1 → (p4 → ((((p5 → p1) → p1) → (p2 ∧ ((((p2 ∧ (((p3 ∨ p1) ∨ p2) ∧ p5)) ∨ True) → (p2 ∨ False)) ∧ p3))) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 → p1) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136792279057758450609404626134 : (((p1 → p3) ∧ ((p3 → p1) → (p1 ∨ ((((p1 → False) ∧ (((p5 ∨ p4) ∨ p5) ∨ p3)) ∨ (False ∨ p4)) ∨ p1)))) ∨ (p2 → (p3 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148592705130766407483236358527 : ((((p1 → (p1 ∨ p4)) → (p5 → ((p5 → p2) → p1))) ∨ ((((True ∨ p2) ∨ p5) ∨ (p1 ∧ p3)) ∨ p3)) ∨ (p2 ∨ (True → (p5 ∨ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680928182956986406405552236564 : (((((p1 → True) ∧ (p5 → (((p1 → False) ∨ False) ∨ (True ∨ (((p1 ∨ (p2 → p3)) → p2) ∨ p3))))) → (((p4 ∨ p2) → p4) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343601938043204036567959748331 : (p2 → ((p4 → p1) → ((False ∧ ((p4 → (p1 ∨ True)) → (p4 ∧ p1))) ∨ ((((p5 ∨ p1) ∧ False) ∧ ((False ∨ (p2 ∧ p5)) → p4)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44886251121602088685424662606 : (((((True ∧ p2) → p3) → (p1 ∨ ((((False → p4) → ((False → p2) → (p1 → ((p3 ∧ p4) ∨ p1)))) → False) ∨ (p3 ∨ p3)))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



