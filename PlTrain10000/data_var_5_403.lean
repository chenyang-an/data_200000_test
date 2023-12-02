variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263796302839443634221784496096 : (True ∧ ((((p2 → ((True ∧ p1) ∧ p1)) → (((p3 ∨ True) ∧ p2) → p2)) → (p2 ∧ p4)) ∨ (True ∨ ((False ∧ (p3 → p2)) ∧ (p5 ∨ p2))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301223303462426454267774687902 : (False ∨ ((True ∧ (True ∨ (p3 → (False ∨ p2)))) ∧ (p4 → (p4 → ((((False ∨ p1) ∨ ((p1 ∨ (p5 ∧ (p1 ∨ p5))) ∧ p1)) ∨ True) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310796851770007379391573159152 : (p2 ∨ ((True ∧ (p5 ∧ p1)) ∨ ((p2 ∨ ((p5 → ((True → p2) ∨ p4)) → (p5 ∧ ((False ∨ (p3 ∧ (p4 ∨ p5))) ∧ False)))) → (p5 ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309315781471849338901210682272 : (p2 ∨ (((p1 ∨ ((((p5 → p2) → p5) → ((p3 ∧ ((p1 ∧ (True ∨ False)) ∧ p4)) ∨ ((p5 ∨ p2) → False))) ∧ True)) ∨ False) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55055713771490722163941003433 : (((p1 ∨ ((p1 → p1) ∧ (p3 ∧ p2))) ∧ ((p3 ∧ True) ∧ (((True ∧ p4) ∧ False) ∧ (p5 → ((p2 → (False ∧ False)) ∨ (p1 → True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303946114292456984961112526257 : (p1 ∨ (((((p5 ∧ p3) ∧ p3) ∧ p3) ∧ (p1 → ((True ∨ (False → (p2 ∨ False))) → (p4 ∨ (p1 ∧ ((p4 ∧ (p3 → p3)) → p1)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299096134104209708001651410873 : (False ∨ ((((((p4 ∨ (True ∨ (p2 ∧ (False → p3)))) ∧ p3) → (False ∨ (True ∨ ((p2 ∨ p3) ∧ p2)))) ∨ (p5 ∨ (p3 ∨ p1))) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203076171757908971224261465893 : (((p5 ∨ p5) → ((p5 ∨ p3) ∨ True)) ∧ (((False ∨ ((p1 ∧ p3) ∧ ((p3 ∨ ((False ∧ p4) → p4)) ∨ (p2 ∨ p5)))) ∨ (p1 → p3)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147180016061095560330948235817 : (((p2 ∨ ((((True ∨ p5) ∧ ((p2 → p5) ∨ (p4 → False))) ∨ (p3 ∨ (p4 → (p1 → p2)))) → False)) ∧ False) ∨ (((False ∨ p4) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593072441406336090191142405059 : ((((((((False ∨ True) ∨ p3) → ((True ∨ True) → (p5 → (((p4 → (False ∨ True)) ∨ False) ∨ p2)))) → p5) ∨ ((False ∨ p3) ∧ p2)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54027347522257822054873987309 : ((((False → ((p3 → (False ∧ p4)) → p3)) ∧ (p2 ∨ False)) → (((p4 → (p5 ∧ p2)) → ((p5 → True) ∨ p2)) → (p4 ∨ (p1 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791345515652812541146589044454 : (((True → ((((((p2 → p3) ∨ (False ∧ (p4 → ((False ∧ ((p5 → p3) ∨ False)) ∨ False)))) ∧ (p4 ∨ p1)) → p2) ∨ (p3 ∨ True)) ∨ p2)) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646160344487105544503712742850 : ((((False → (((((p4 ∨ False) ∨ (p1 ∨ p2)) ∧ (((p3 ∨ False) → p1) → False)) → ((p3 → (p1 → False)) → (p5 → p4))) ∨ p3)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745630212824578960696115109448 : ((((True ∨ p3) → ((p2 ∨ ((p2 → (((False ∨ (p3 ∨ (((p1 ∧ (p5 → p1)) ∨ p4) ∨ p2))) ∨ p1) ∨ True)) ∨ (p1 ∨ p5))) ∨ True)) ∨ p2) ∧ True) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322478576529079947416015290764 : (p5 ∨ (((False → p4) ∧ ((p4 ∨ (((p4 ∨ (p3 ∨ p4)) ∧ (p4 → (((p5 ∨ True) ∨ ((False ∧ p2) ∧ False)) → True))) ∧ p3)) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75820504884874721508410750035 : (((((p5 ∧ p4) ∨ (p3 ∧ (p4 ∨ ((((p4 ∨ p5) ∧ True) ∨ ((((p5 → True) ∧ p5) ∨ (True → p3)) ∨ p1)) ∨ True)))) ∨ True) → p4) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ p4) ∨ (p3 ∧ (p4 ∨ ((((p4 ∨ p5) ∧ True) ∨ ((((p5 → True) ∧ p5) ∨ (True → p3)) ∨ p1)) ∨ True)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340776655780073252249790495124 : (p2 → ((((((p2 ∨ (True ∧ True)) ∧ p3) ∧ ((p5 ∨ True) ∨ (p1 ∧ (((p2 → (p4 ∨ p1)) → (p5 → p2)) → p5)))) → p2) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749680608420892800628916967755 : (((True ∧ (((((p2 ∨ p5) → p4) → (((p3 ∨ (((False ∨ p4) ∨ p5) ∨ (p3 → True))) ∨ (p1 → p4)) ∨ p5)) ∧ (p1 ∨ p5)) ∨ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115389280475384919392037061418 : ((((p4 ∨ True) ∨ (p5 ∨ ((p1 ∨ p2) ∧ p5))) ∧ (((p1 ∧ p4) ∧ (p2 ∨ p3)) ∨ (((p1 ∧ (p3 ∧ False)) → p1) ∨ p5))) ∨ (p3 ∨ p4)) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172526331832966386425223051559 : (((False ∨ (p1 ∨ p3)) ∧ (p5 → (((p1 ∨ p1) → False) ∨ (p5 ∨ (True → p1))))) ∨ ((((p2 ∨ p5) → p2) ∧ (True → p4)) → (p4 ∨ True))) := by
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
theorem thm_5_vars_695810758761605419591463869533 : (((((p2 ∧ (p4 ∨ p4)) → ((p4 ∨ (((p5 → p2) ∧ p5) ∨ p4)) ∧ False)) → ((p3 ∨ ((p1 ∧ ((True ∧ p1) ∨ p3)) ∨ p5)) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_1112525926091623995701945243 : ((((((p1 ∨ (((False ∧ p3) ∧ p3) → p4)) ∨ (p3 → p5)) → p5) ∨ True) → (True ∧ (p4 ∧ (p1 ∧ (True → (False ∧ p5)))))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 ∨ (((False ∧ p3) ∧ p3) → p4)) ∨ (p3 → p5)) → p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346291014093808917985951728457 : (p3 → (((((((p1 ∨ p5) ∧ (((((p3 → p1) ∨ p3) → False) ∨ (True → p5)) ∧ (False → p1))) ∧ p4) ∨ p3) ∧ p4) ∨ True) ∨ (p4 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621179931551125544921468075889 : ((((True ∧ ((p5 ∧ ((p1 → ((p2 → (((p3 ∨ (True ∧ ((True ∧ True) ∧ p5))) ∨ p4) ∨ p4)) ∧ (p2 ∧ p2))) → p2)) ∧ False)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_259460636752858838077613473829 : ((False → p4) → ((((True ∨ p5) ∧ p4) → p3) → (((((False ∨ p4) ∨ True) ∨ ((p1 ∧ False) ∧ True)) → p1) ∨ (True ∧ (True ∨ (p2 ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690179591764653173523253562460 : ((((p3 ∨ ((p4 ∧ ((((((p4 → p1) ∧ p3) ∨ p5) ∨ p4) ∧ False) ∧ p4)) ∨ False)) ∨ (False ∨ (p3 → (p4 → (p3 ∧ (p4 ∨ p4)))))) ∨ p5) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138400254050748484815868225966 : ((p4 → (p2 → (((((p3 → p2) ∨ (p3 ∨ False)) → (p3 → p5)) ∨ (p1 → False)) ∨ (p5 → ((p1 ∨ p1) ∧ p4))))) ∨ ((p4 ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117758728445210501637918134843 : ((p4 ∧ (((False ∨ (p3 ∨ (True → (p1 → (((False → p2) ∧ (((p3 ∧ p3) → (p3 ∨ True)) ∨ p4)) ∨ p3))))) → p2) → p3)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148807244605546943460323211758 : ((((p2 ∨ (p3 → (p1 → p1))) → False) → ((p5 → (p1 ∧ ((True ∨ False) ∨ p4))) ∧ ((p1 ∨ p3) ∧ p5))) ∨ (True ∧ ((True ∨ p5) → True))) := by
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
theorem thm_5_vars_53160218754649174007575258710 : ((((p1 ∧ ((p3 ∧ (((p5 ∨ p5) → True) ∧ p5)) ∨ p2)) ∨ p2) ∨ (True → (p4 ∨ ((p4 → p4) ∨ ((p2 ∧ (p5 → p5)) → False))))) ∨ p4) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63136213244819549346791493200 : ((p5 ∧ (((p3 ∨ p5) ∨ ((((True ∧ p3) ∨ (p2 → p2)) ∧ False) → ((((p4 → p2) ∨ p1) → ((False ∧ True) ∨ p1)) ∧ False))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67977402845917936625957257247 : ((p2 → (((False → p3) → p5) → ((((p4 → p1) ∧ (p3 ∨ ((p3 ∨ (p4 ∨ p1)) ∧ p4))) ∨ ((p3 ∧ p2) ∧ p2)) ∧ (p3 → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165641793071635127660050646923 : (((p5 ∨ (((True ∨ True) ∧ p2) → p5)) ∧ (p1 → ((False ∧ (p4 ∨ (p5 ∨ p4))) → True))) ∨ (p4 → ((p3 ∧ (p3 ∧ (p3 ∨ p1))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622933505599607960494683279746 : ((((p5 ∧ ((((((p4 ∨ False) ∧ (p5 → (False ∧ p2))) ∧ p2) ∧ (p2 ∨ False)) → p1) ∧ ((p4 → False) ∧ ((False ∨ p3) → False)))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67792785982653557043939144004 : ((p2 → (((p3 → (p1 ∨ (True ∧ (((True → ((p5 → p3) → False)) ∧ (False ∨ p5)) → ((p4 ∧ (p3 ∨ True)) → p2))))) ∨ p5) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38604716643662365766709731865 : ((((((p3 ∧ p3) → (p2 ∨ p4)) ∧ (p4 → p5)) ∧ (True → (p4 → ((p5 ∨ ((p5 ∨ (p1 → p4)) → p1)) ∨ (True ∧ p1))))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636078924467823161286323092430 : (((((p5 ∨ ((((False → (p3 ∨ p2)) → p5) ∧ (p2 ∨ ((p5 ∨ False) ∧ p3))) ∨ p2)) ∧ (((p1 ∧ p5) → (p3 ∧ p1)) ∨ p3)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22931634086639641327999689921 : (((p2 ∧ (p4 → (True ∧ (True ∧ p1)))) ∨ ((p1 ∨ ((p2 → False) → p4)) → (p1 → ((((False ∧ p3) → p1) ∧ (p2 ∨ p4)) → p1)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248038056980244934279505595160 : ((p1 ∨ p5) ∨ (((p3 ∧ (p2 ∧ p2)) → (p4 → (p2 ∨ (p4 ∧ p3)))) ∧ ((False ∨ ((False → p5) → ((p4 → (p4 → p5)) ∨ True))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62653855581611213850218137619 : ((p4 ∧ (((((p4 ∨ p4) ∨ (((True ∨ p1) ∨ (True → (p5 ∧ p2))) ∧ (True ∧ p4))) → (((p5 → p5) → p3) → False)) → p3) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612312733726381092115433632000 : (((((p2 ∧ (((((p1 ∨ (p4 ∨ (p1 ∨ p5))) ∧ (((True ∧ p4) ∨ p1) ∨ p3)) → p4) ∨ False) ∧ (p1 ∧ p2))) ∧ (p1 ∧ True)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_147384120482199780322581097498 : (((((p1 ∨ (p1 ∨ ((p2 ∨ (p5 ∧ p2)) ∧ False))) → p4) → ((p5 ∧ ((p1 ∧ p4) → p3)) ∧ p3)) ∨ p4) ∨ ((True ∨ p3) → (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113359352887573917471557300853 : (((p4 ∧ ((p3 ∨ False) ∨ (((p2 → ((False ∧ p3) → (p3 ∨ p4))) ∨ (((p1 ∧ p3) ∧ p4) ∨ p2)) ∧ p5))) ∧ (p4 → p2)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118239886098231589809131063707 : ((p1 ∨ ((((True → (False ∧ ((p1 ∨ p2) ∨ (p1 ∧ p1)))) ∨ (p4 ∧ ((True ∧ p4) ∧ (p3 ∧ False)))) → p3) ∧ (p3 ∨ p5))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65292254660450966777332863545 : ((p3 ∨ (((p2 ∨ (False ∨ p2)) → (False ∧ ((False ∨ (((p4 ∨ p5) ∨ p5) → ((p4 → p5) → False))) → (p1 ∧ False)))) ∨ (True ∨ p4))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227730942666951389659513258221 : ((p1 ∧ (True ∨ p5)) ∨ ((p1 ∨ ((p3 → True) → (((p3 ∧ (((p4 ∨ (True → (p4 ∧ p4))) ∨ (p4 ∨ p2)) ∧ p3)) ∧ p5) ∧ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80259388762366131207434494669 : ((((p1 ∨ (((p4 ∨ True) ∨ True) → ((p1 ∨ (p5 → p5)) ∨ ((True ∨ (p1 → p3)) ∧ (p2 ∨ p1))))) ∨ (p5 ∧ p3)) → (True → False)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ (((p4 ∨ True) ∨ True) → ((p1 ∨ (p5 → p5)) ∨ ((True ∨ (p1 → p3)) ∧ (p2 ∨ p1))))) ∨ (p5 ∧ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
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
        -- Implications on the right can always be decomposed.
        intro h6
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h13 := h11 h12
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65221815524323369739074122442 : ((p3 ∨ (((True ∧ p1) ∨ (((((p5 → True) ∨ p3) ∧ p2) ∧ (True → ((p1 ∨ ((p1 ∨ p3) ∧ True)) → (False ∧ True)))) ∨ False)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172459044311178628308681834210 : (((p4 ∧ ((p4 ∨ False) ∨ p3)) ∨ (((p4 → (False ∨ p2)) → p5) → (p1 ∨ p4))) ∨ (((p3 ∧ True) → (p4 ∨ ((p3 ∧ p3) ∨ p4))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130423232438001212287135050276 : (((((p3 → (p3 ∨ ((((p5 ∧ p3) → p1) ∨ True) ∧ (True ∧ p5)))) ∨ (p2 ∧ True)) → p2) ∨ (p5 → (p4 ∨ True))) ∧ (True ∨ (False ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206047806471675911680003110525 : ((p2 ∧ (p5 ∨ ((p4 → p5) → False))) ∨ ((((True → ((p3 ∧ (p5 → p2)) ∧ ((p5 ∧ (p4 ∨ True)) → p2))) ∧ (p4 → p1)) → True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153258550701384893428849800269 : ((False ∨ ((True → (True ∧ (((p2 → (False → p2)) → p1) ∧ p5))) ∧ (p4 → ((p1 ∨ p4) → (p5 ∨ p5))))) → (p1 → ((p5 → p3) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : p5 := by
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h10 := h6 h9
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h8
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345028417052348944544853323296 : (p3 → ((((p1 ∧ (((True ∨ (((p4 ∨ p3) ∨ ((p1 → p3) ∨ (False ∨ p2))) ∧ p1)) ∨ (p5 → p5)) ∨ p3)) ∨ p1) → (p4 ∨ True)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h12 =>
            -- Disjunctions on the left can always be decomposed.
            cases h12
            case inl h13 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h13
            case inr h14 =>
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
              -- Disjunctions on the left can always be decomposed.
              cases h17
              case inl h18 =>
                -- False on the left can always be used.
                apply False.elim h18
              case inr h19 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153675269779600015819891267261 : ((p2 → ((p3 ∨ (((True → p1) → (((p4 → p5) ∨ (p3 → True)) → p2)) → p5)) ∧ (p3 → (p4 ∨ p3)))) → ((p1 ∧ (False ∨ p4)) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336262441307395528859155909295 : (p1 → (((False → (p1 ∧ (p2 → (((p4 → (p4 ∧ p3)) → p3) → (p3 ∧ False))))) ∧ (p1 → (p3 ∨ (p3 → ((p4 → p1) → False))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156853432757296627111729071424 : ((((((((((p4 ∧ p5) ∧ p1) ∧ p1) ∨ (p5 → p2)) ∧ (True ∨ p3)) ∨ True) ∧ True) ∧ p5) ∨ p5) ∨ ((True ∨ ((p5 ∨ p3) → p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118467008410452640943901544846 : ((p3 ∨ ((((False ∨ (p5 ∨ p2)) ∨ (p5 → (False → (False ∧ (((True ∧ (False ∧ (True → p4))) → False) → p4))))) → False) → p3)) ∨ (p4 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ (p5 ∨ p2)) ∨ (p5 → (False → (False ∧ (((True ∧ (False ∧ (True → p4))) → False) → p4))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47298319715923784920764215766 : (((((p5 → p1) → p4) ∧ (p4 ∨ (((False ∧ (p3 → ((False → p3) → p2))) ∨ (False ∨ (p2 ∨ (p2 ∧ p3)))) ∧ p4))) ∨ (p4 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137313971821933102695830639522 : ((p2 ∧ ((p1 ∨ (((p5 ∧ p5) ∧ p2) ∧ (True ∨ p5))) → ((((p1 → p3) ∨ (p5 ∧ False)) ∧ (p5 → p4)) ∧ p2))) ∨ (p3 → (p1 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755453844292813002100781565863 : (((p1 ∧ (((p5 ∧ p4) ∧ ((True ∧ ((p4 ∧ (p5 → p1)) ∧ p1)) ∨ (((p1 ∨ (p1 ∧ p5)) → (p2 ∧ (p4 ∧ p4))) → p5))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193277514725845879494366603846 : ((((p2 ∨ False) ∧ True) ∨ ((p1 → (p2 → p2)) ∨ True)) → (p3 → (p3 ∧ ((((p5 → True) → (((p2 ∨ p2) ∧ p4) ∧ p4)) ∨ True) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h18 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136480229388964936656301003335 : ((((p5 ∧ True) ∨ p3) ∧ (((p4 ∨ p3) ∨ (p1 → (True ∨ p3))) → (((p1 → False) ∨ (p1 ∨ False)) → (p2 → p5)))) ∨ (p1 ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707769917955625571638553413886 : ((((True ∧ ((p2 → (p2 ∨ (p5 → p4))) → p2)) ∨ (p5 ∨ (((p4 ∧ ((False ∨ True) ∧ (((False ∨ p4) → False) ∧ p3))) ∧ p1) → False))) ∨ False) ∧ True) := by
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
  cases h6
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h7.left
    let h11 := h7.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h12 : (False ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h12
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185845605826006179626260523441 : (((((((p5 ∧ p4) → False) → p4) ∧ (p2 ∨ p5)) ∨ p3) ∧ p3) → (((p3 → True) ∧ True) → ((p4 → p1) → (p4 → (p1 ∧ (p4 ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h13 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h14 := h3 h13
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h16 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h17 := h3 h16
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h18 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h19 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h20 := h3 h19
    -- One of the premise coincides with the conclusion.
    exact h20
  -- Conjunctions on the left can always be decomposed.
  let h21 := h2.left
  let h22 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h23 := h1.left
  let h24 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h23
  case inl h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h29 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h30 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66591309837429793705828099407 : ((True → (((((((p4 → p5) ∧ True) ∨ (p3 ∧ (p2 ∨ p5))) ∨ p3) → (p4 ∧ True)) ∨ (True ∧ (p4 ∧ p4))) ∨ ((True → p1) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42289531332765784545810764659 : (((p2 ∧ (((p3 ∧ ((((False ∨ ((p2 → p5) ∧ p5)) → ((p4 ∨ p3) → (p4 ∨ p4))) ∧ True) ∧ (p3 ∨ p1))) ∨ p1) ∧ p5)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809792959022915411574587469486 : (((p5 → (((p1 → False) ∧ ((((p4 ∨ (p5 → (True ∧ p3))) → ((p5 ∨ (p2 ∨ (p4 → p2))) ∧ False)) ∨ p5) → p2)) ∨ (p4 → p5))) ∨ False) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149792316711792410172497269040 : ((False ∨ ((p1 ∨ (p1 ∨ (p5 → True))) → ((((p3 ∨ p4) ∧ (True ∧ True)) ∨ False) ∨ ((False → p3) ∨ p1)))) ∨ (p3 ∧ (p3 ∧ (p5 ∨ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247427507766842931887671316971 : ((False ∨ p2) ∨ (((((((p5 ∧ p2) ∧ ((True ∨ p5) → True)) ∧ False) → p2) → False) ∧ (p5 ∨ p4)) → ((True ∧ (p5 ∧ (True ∨ p3))) ∨ False))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : ((((p5 ∧ p2) ∧ ((True ∨ p5) → True)) ∧ False) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h6
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146992100885800511990215038804 : ((((False → (p3 ∨ (p4 → ((p2 → (p3 ∧ (((p4 ∨ p5) ∨ p5) → (p3 ∨ False)))) ∨ p2)))) → False) ∧ p2) ∨ ((p4 ∧ p4) ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50389508577277680180472032329 : ((((p4 ∨ False) ∨ ((p5 → ((False ∨ ((p3 ∨ (False → (True → (False ∧ p2)))) ∧ p2)) → p1)) ∨ False)) ∨ ((p5 → (p2 → True)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320457940706988729590844535871 : (p4 ∨ ((True → False) → (True ∧ (((((p2 ∧ p2) → False) ∨ (p4 ∧ (p2 ∧ (True ∧ ((p4 ∧ p2) → True))))) → (p1 → (False ∧ p2))) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57336258506229173669845135403 : (((p1 ∧ (False → p5)) ∨ ((p1 ∧ ((True ∧ True) → p2)) ∨ ((p2 ∨ (((False → True) → False) ∨ ((p5 ∧ (False ∧ False)) ∨ p5))) ∨ True))) ∨ p4) := by
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
theorem thm_5_vars_262324532054445762454384497967 : (True ∧ (((p3 → ((p5 → p2) ∧ ((p1 ∨ p3) → p2))) ∨ (True ∧ ((p3 ∨ (((True → (p4 ∨ (p5 ∨ False))) ∧ p4) ∧ True)) ∨ p4))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685752628535473704089596410923 : ((((((p3 ∧ ((((p3 ∧ p1) ∨ (p2 → (False ∧ False))) ∨ (True ∧ False)) → p4)) ∧ False) → True) → ((p4 ∨ p1) ∧ (False → (p3 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61435477227754238661235807631 : ((p1 ∧ (((p4 ∧ p4) ∨ (((False → ((((False → (p5 ∨ p4)) → p5) → p4) ∨ True)) ∨ (p2 ∨ p2)) ∧ ((p2 ∨ p4) ∨ p4))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602163188360278183966642782187 : ((((p5 ∧ ((p4 ∨ p3) ∧ ((p1 → False) ∧ ((p3 → False) ∨ (True ∨ (False ∨ (p3 ∧ ((p4 → p1) → (p3 ∧ (p4 ∧ p1)))))))))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117036962345478270713025253874 : (((p3 ∨ p1) → ((p5 ∧ ((((p5 ∧ ((p2 ∨ p5) ∧ True)) ∧ p1) → True) ∧ p2)) ∧ ((((p4 → False) ∧ p3) ∨ True) ∧ False))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_237923495385815236017124530492 : ((True ∨ True) ∧ (p2 → (((((((False ∧ p5) ∨ (p5 ∨ p1)) ∧ p5) ∧ p5) → True) ∨ True) → ((((p5 ∧ False) ∨ (p1 ∨ p2)) ∨ p1) ∨ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722808534376274334598949229051 : (((((True ∧ p5) ∨ p3) ∧ (((p2 ∧ p5) ∧ p4) ∧ ((((False ∧ p5) ∨ (False ∧ p2)) ∧ (p1 → (True → p2))) ∧ (p2 → (p5 ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208084200882420963913744497776 : (((p3 → (p5 ∨ p3)) ∨ (p2 → True)) → ((((False → (p5 → p1)) → ((p5 ∨ (p2 → (p4 → True))) → ((p4 ∧ True) ∨ p3))) ∧ False) ∨ True)) := by
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
theorem thm_5_vars_37406270474317688599896885579 : ((((((((p1 → False) ∧ p4) ∧ ((((p5 ∨ True) ∨ p1) → (p2 ∨ ((p3 ∧ p3) ∨ p2))) ∧ p3)) ∧ p3) ∨ (p2 ∨ True)) ∨ p5) ∧ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_260060849051082665042390753657 : ((p2 → False) → (((p2 ∨ p4) ∨ (p2 ∧ (((p5 ∨ False) ∧ (p3 ∨ False)) ∨ (True ∨ p1)))) → ((p1 ∨ (True → p5)) → (p1 ∨ (p3 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h15 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h4
          case inr h16 =>
            -- False on the left can always be used.
            apply False.elim h16
        case inr h17 =>
          -- False on the left can always be used.
          apply False.elim h17
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h20 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h24 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h23
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h25 := h1 h24
        -- False on the left can always be used.
        apply False.elim h25
      case inr h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h26
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h30.left
        let h32 := h30.right
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h33 =>
          -- Disjunctions on the left can always be decomposed.
          cases h32
          case inl h34 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h34
          case inr h35 =>
            -- False on the left can always be used.
            apply False.elim h35
        case inr h36 =>
          -- False on the left can always be used.
          apply False.elim h36
      case inr h37 =>
        -- Disjunctions on the left can always be decomposed.
        cases h37
        case inl h38 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h39 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h28
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h40 := h1 h39
          -- False on the left can always be used.
          apply False.elim h40
        case inr h41 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217098186526174208489095048909 : ((((p4 ∧ True) ∨ p4) ∨ p3) → (((((p3 → (p1 ∧ p2)) → p2) ∧ p1) ∨ ((True ∨ p3) ∧ ((False ∧ p2) → True))) ∨ ((True ∨ False) → False))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765857155060807010405387858409 : (((p4 ∧ ((((p5 → p4) → p5) → (False ∨ p3)) ∨ ((True ∧ p3) ∧ (((p1 ∨ ((p5 ∧ p3) → (p2 ∨ (p3 ∨ p3)))) ∧ p3) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614259042041704341445859089114 : ((((((p1 → (p5 ∨ (((p5 → True) ∧ False) → ((p2 → p4) → (p5 ∨ p4))))) → (p2 ∧ (p4 ∧ p4))) → (p5 → (p4 ∧ p1))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699844352154025687985962616814 : (((((p1 → ((p5 ∨ (p3 ∧ p4)) → (p2 ∧ p4))) → (p1 → p3)) → (((((p5 ∧ ((p1 ∨ p5) ∧ True)) ∨ p2) ∨ p5) ∧ p3) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116458880582051765283982229165 : (((True ∧ p5) ∧ (((((((p5 ∧ p5) → (False ∧ False)) ∨ False) ∧ (p4 ∧ p4)) ∧ False) ∨ ((p3 ∧ True) → p4)) ∧ (False ∧ p3))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630804883905540554026331203703 : (((((((((p5 → (((((p3 → True) ∧ (p2 ∨ p3)) ∨ (p1 ∨ p5)) ∧ p4) → (p1 → p2))) ∨ False) ∨ True) ∧ False) ∧ p4) → p5) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763033451660098959305422513553 : (((p3 ∧ (((p1 → False) → p1) ∧ ((p5 ∨ (p5 → (((p4 ∧ p1) ∨ ((p5 → (p1 → p3)) ∧ p2)) ∧ (p5 → p5)))) ∨ (p4 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164790223251577938185770450799 : ((((((True → p2) ∨ False) → p3) ∨ ((((p1 ∨ p2) ∧ (p4 ∨ p5)) ∨ p1) ∧ p4)) ∨ p3) ∨ ((p2 ∧ (p1 ∨ (p5 ∧ (p1 ∧ p1)))) → p2)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247618494778315741261574158732 : ((False ∨ p5) ∨ (((p4 ∨ False) ∨ (p2 → p4)) → (((((p1 ∧ ((p2 ∧ p1) ∨ (p2 ∨ p3))) ∨ p3) → True) → p1) → ((p4 ∨ p1) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (((p1 ∧ ((p2 ∧ p1) ∨ (p2 ∨ p3))) ∨ p3) → True) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307503707192595409489220903325 : (p1 ∨ (True → (((((True → p4) → p2) ∨ ((p3 ∨ ((p4 → (p4 → False)) → False)) ∨ False)) ∧ True) ∨ ((True ∨ p4) ∨ (False → (True → p5)))))) := by
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
theorem thm_5_vars_121593869973804346012861512782 : (((((p5 ∧ True) ∨ (((True → (p1 ∨ ((p2 ∧ p4) ∨ (p4 ∧ p4)))) → p1) → (True → p5))) ∨ (p5 → (p1 ∨ True))) → p4) → (False ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ True) ∨ (((True → (p1 ∨ ((p2 ∧ p4) ∨ (p4 ∧ p4)))) → p1) → (True → p5))) ∨ (p5 → (p1 ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41431710257566430118851995937 : ((((((p5 → ((p1 ∨ True) ∧ (p5 → (p2 → p3)))) ∧ p3) ∨ (p1 → p1)) → (p4 → ((False → p5) → ((p1 ∨ p3) ∨ p1)))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60784826964740342453570189868 : ((True ∧ ((p1 → p4) → (p3 ∨ (((p4 ∨ (False → True)) → (((p2 ∨ (p4 → (p5 → p1))) → True) → (p3 → (p5 → p2)))) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355579719653895039904198182043 : (p5 → (((((((False ∨ p5) → (p3 ∧ (p2 ∧ p4))) ∨ (p1 ∧ p4)) ∧ p5) ∧ p3) → (((p3 ∧ (p2 ∧ p3)) ∨ p5) ∨ True)) ∨ (p5 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223594986263736533171198883857 : ((p1 ∨ (True ∨ p1)) ∧ (((((((p4 → p4) → p2) → False) → p4) → p5) ∧ (p4 ∨ p4)) → (p2 ∨ (p4 ∧ (p5 → (p2 ∨ (p4 → p5))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619223040825782281069121707501 : (((((p4 → (p2 ∨ p2)) ∨ ((p4 ∧ p2) ∨ (p4 ∨ (p4 ∧ ((True → p5) ∧ (p1 ∨ (((p3 → p2) ∧ (p3 ∨ p4)) ∧ p2))))))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144555038625239077892712331179 : (((((p3 ∧ (p3 ∧ p1)) ∧ p5) ∨ ((p3 ∨ (p3 ∧ (p2 → ((p1 ∨ p1) ∧ p1)))) ∧ p1)) ∨ (True ∨ p1)) ∧ ((True → (p5 ∨ False)) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



