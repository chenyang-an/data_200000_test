variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306048879405905652865946848353 : (p1 ∨ (((p3 → p3) ∧ (p4 → p3)) → (((p1 → p3) ∨ (((p1 ∨ (False ∨ (p2 → (((p1 → p5) ∨ True) → True)))) ∧ True) ∨ p5)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171308188067766091375843386927 : ((((p3 ∧ ((False → ((p2 ∨ p5) → (False ∧ True))) → (p2 ∧ p4))) ∧ False) ∧ False) ∨ (p3 → (((p4 ∧ p1) → p4) → ((p5 ∧ p4) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61787870113737225026395394456 : ((p2 ∧ ((False ∨ (((p4 ∧ (p2 ∧ (True ∨ ((False ∧ (((p1 ∧ True) → False) ∨ p1)) ∧ p3)))) ∧ ((p5 ∨ p2) ∨ p5)) ∧ p3)) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345321461060962966553698723642 : (p3 → (((((p3 → p5) ∨ (((((p5 → p5) ∨ p4) ∧ p5) ∧ (((((p1 ∨ p4) → p4) ∧ p2) ∨ p4) ∨ p5)) → p3)) → p1) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228968331155761468571220431963 : ((p4 ∨ (p2 → p5)) ∨ (((p1 ∧ (p1 ∧ p2)) ∨ (p1 ∧ p1)) ∨ (((p4 ∨ p3) → (p5 → False)) → ((p3 ∨ (False → p3)) ∨ (p4 ∨ p3))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112295563922453928542475350052 : (((p1 → (((p3 ∧ ((True → p1) ∨ p2)) ∨ (((p4 → p3) ∨ ((p5 ∧ p5) ∧ p4)) ∨ ((p3 → p1) ∨ True))) ∨ p4)) ∨ True) ∨ (p2 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157026387349437274096655904195 : ((((p5 ∧ p1) ∨ ((True → ((((p2 → False) ∧ True) ∨ (p4 → (p1 ∨ p3))) ∧ p2)) ∨ True)) ∨ p3) ∨ (p4 → ((p3 → p4) ∧ (False ∧ False)))) := by
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
theorem thm_5_vars_619107394576776531496204243697 : (((((p2 ∧ (p4 ∨ p1)) ∨ (((p3 ∨ p3) → (False ∧ (False → p5))) → ((((((p1 ∨ p4) → p4) ∨ p4) ∧ p2) ∨ p2) ∨ p5))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_340941861712615817864984734002 : (p2 → ((((p1 ∨ True) → (False → False)) → (((p5 ∧ True) ∨ p3) → (((((p2 ∧ p2) ∧ True) ∨ (True → (p5 ∧ p3))) → p1) → p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166819089133551443546747765680 : ((((((False → p5) → (False ∧ (p2 ∨ (p3 ∧ ((p1 ∧ p2) → p2))))) ∧ True) ∨ p3) ∧ p5) → (((p5 ∨ p4) → (True ∧ p4)) → (p1 → p4))) := by
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
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : (False → p5) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h11 := h7 h9
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : (p5 ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610021951537918207531432443429 : (((((((True → ((False ∧ (((p2 ∧ ((p2 → ((p3 → p5) → (p4 ∧ p2))) ∧ p1)) ∧ p3) ∨ p2)) ∧ p1)) → p4) ∧ True) → False) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_642556735221423986345883294395 : ((((p1 ∧ ((((p4 ∨ p2) ∨ p4) → ((True ∧ (((True ∧ (p3 → (p3 → ((p3 ∧ p2) ∧ p5)))) → False) → p2)) ∧ False)) ∧ p4)) → p5) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((p4 ∨ p2) ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305154996789835236646857131151 : (p1 ∨ ((((p1 → (((((((p4 → (False ∧ p1)) ∨ p5) → p2) → p5) ∧ False) ∨ p3) ∨ True)) → p3) ∧ p3) ∨ (p1 → ((p4 ∨ p2) → p1)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145333556813266198330307532604 : ((((((False ∧ True) → p1) → p1) → True) → (((((((True ∨ True) ∧ p1) ∧ p3) ∨ False) ∨ False) ∧ p1) ∨ True)) ∧ ((False ∧ (p1 ∧ False)) → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192781378345828386911127666440 : (((True ∨ ((p5 → p1) → (True ∨ (p4 ∨ p5)))) → False) → (((False ∧ (p4 ∧ p5)) ∨ (p2 ∧ (p4 ∨ ((p2 ∨ False) ∧ True)))) ∧ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ ((p5 → p1) → (True ∨ (p4 ∨ p5)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43714716763416188586706692719 : (((((True ∧ (p3 ∧ p3)) ∧ (p5 ∧ ((p4 → p5) ∧ (((p4 ∨ False) → p3) ∨ (((p5 ∨ p2) ∨ (p3 ∧ p2)) ∧ p4))))) → p1) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616440950721246544440674557598 : (((((((p1 → p4) ∧ (((False ∨ True) ∨ p3) ∨ p3)) → (p3 ∧ True)) → (((p2 → (p1 ∧ (False ∨ p3))) ∨ (p5 → False)) ∨ p1)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121403188134157119603279543480 : (((((p5 ∧ False) ∧ ((p1 ∧ ((False → (p3 ∧ p4)) ∧ p2)) → (((p5 ∧ p4) ∨ p2) ∨ (p5 → (True ∨ p4))))) ∨ True) → False) → (p2 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p5 ∧ False) ∧ ((p1 ∧ ((False → (p3 ∧ p4)) ∧ p2)) → (((p5 ∧ p4) ∨ p2) ∨ (p5 → (True ∨ p4))))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37421135302948882723060897837 : ((((((False ∨ (((((p1 ∧ True) ∨ (True ∨ (p5 ∨ (p3 ∨ p4)))) → True) ∧ p5) ∧ p5)) ∨ p3) ∧ ((True ∨ p3) ∨ p4)) ∨ p2) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346397126288408019829761327010 : (p3 → ((p5 → ((False ∨ (False ∧ ((p1 ∨ ((p3 ∨ (p2 ∧ p1)) ∨ p3)) ∧ p2))) ∨ (((True ∨ (p2 ∨ False)) ∧ p1) ∨ True))) ∨ (p3 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117389533230980815649469784223 : ((p1 ∧ ((True → (((False → (p1 → ((p2 ∨ p1) → (True ∨ p4)))) ∧ (False ∧ p4)) ∨ (p3 ∧ ((p2 ∧ False) → p3)))) ∧ p5)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_396106761920308304537346013514 : ((((p4 ∧ ((((p4 ∧ (p1 → (((p5 ∨ (p5 → p1)) ∧ p2) ∨ (True → p3)))) → (p3 ∨ False)) ∧ False) ∧ (False ∨ (False ∨ p1)))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_146906970675819162401285102739 : (((((((((p3 → ((True → p1) ∨ (p2 ∧ False))) ∧ p1) → p1) ∨ (p5 ∨ p4)) ∧ p4) → p3) ∧ p1) ∧ p1) ∨ ((p4 ∧ (p2 → True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38784049193335095684935308870 : (((((p2 ∨ p4) ∧ (p4 → p3)) ∨ ((p1 ∨ p3) → ((((p1 ∧ p5) → p4) ∨ (((p2 ∧ p5) ∨ p1) ∧ (p2 ∨ p3))) ∧ p3))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115126622529797558019714781309 : (((((p4 → (p3 ∨ False)) → p4) ∧ ((p2 → p5) ∨ (p5 → p3))) → ((True ∧ (False → (((True ∧ p5) → p2) ∧ p5))) → p1)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606230242924814104747472972419 : (((((((False ∧ p4) ∧ (p1 ∧ (((True → ((False → p3) → (p2 ∨ p5))) ∨ p1) → (((False ∧ p4) ∧ p3) → False)))) ∧ p5) ∧ p1) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338768467396798573185902541446 : (p1 → ((p1 ∧ p5) ∨ (((p1 ∧ (True ∨ False)) → False) ∨ ((((p2 → p4) ∨ (p3 ∧ p2)) ∨ p3) ∨ (p1 ∧ ((p1 → True) ∧ (p5 ∨ True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135654416833056916341591606345 : (((((p5 ∧ p5) → p5) ∧ (p2 → (((p2 ∨ p5) → p1) ∨ ((p4 ∧ p3) ∧ p2)))) → (((False → p2) ∧ p2) → p4)) ∨ ((True → True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48508005808274961015539373832 : (((((p1 ∧ (p1 ∨ ((((((p4 ∧ p4) → (True ∧ p4)) ∧ (p1 ∧ p2)) ∨ True) ∨ False) ∨ p4))) → p4) ∨ p1) ∧ ((p1 ∨ False) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195649464227374544521127368874 : (((False → p3) ∧ (False ∨ (True → (p3 → True)))) ∧ ((((p4 → True) → p5) → ((((p5 → (p1 ∨ p4)) → p1) ∧ (p2 → p2)) ∨ p5)) ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p4 → True) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592344720696451309961041486 : ((((True → False) ∨ (p3 ∨ ((True ∧ ((p1 ∨ p2) → p5)) → ((p4 → p3) ∧ ((p4 ∧ p1) ∧ ((p1 ∧ False) ∧ p3)))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692804669873387501538563353220 : ((((((p2 → False) ∨ False) ∧ ((False ∨ p3) ∧ ((p5 ∧ p1) → (p3 → p4)))) ∧ (p4 → ((p1 ∨ p2) ∨ (p2 ∨ (p2 ∨ (p1 → True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4205190286202208230481954785 : (p5 ∨ (((((p4 ∨ (p4 ∧ p4)) ∨ (p2 ∨ p4)) → (((p4 ∧ p4) ∨ (p5 → ((p1 → p5) ∧ (p3 → p5)))) → False)) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149219799425678780905581664340 : (((p2 ∧ p1) ∨ (p4 → (p4 ∧ (((p3 ∧ p2) ∨ ((p5 ∧ (p1 → (p1 ∨ p4))) ∨ (p3 ∧ p5))) ∨ True)))) ∨ (((p1 ∧ p1) ∨ p1) → p3)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4068452965540217289268945389 : (p2 ∨ (p1 ∨ (p5 → ((((p2 ∨ (p4 → True)) ∧ p4) → False) ∨ (True ∨ ((p4 ∨ p3) → (((p4 → p1) ∧ (p1 ∧ True)) → p5))))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675650505299160824452693698486 : (((((((p2 → (True → ((p3 → False) ∧ (p2 ∨ p5)))) ∨ ((True ∨ p2) ∧ True)) → p3) → (p4 → False)) ∧ (p1 ∧ ((p2 → p1) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245552040857472469362755898272 : ((p3 ∧ True) ∨ ((False → ((False ∧ (p5 ∨ True)) ∧ True)) → (((((p2 → False) ∧ (p2 ∧ (False → (p3 ∨ (False ∨ p3))))) → True) → False) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p2 → False) ∧ (p2 ∧ (False → (p3 ∨ (False ∨ p3))))) → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166025805832382731848018200091 : (((True → p1) ∨ (p2 ∧ ((p2 → (p3 → False)) → ((((p1 ∨ False) → p2) → p3) ∨ p3)))) ∨ ((False → ((p3 → p1) ∧ (p1 → p3))) ∨ p2)) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113615390857429279391244979875 : (((p5 ∨ ((p4 ∨ ((p1 ∧ p3) ∧ p5)) ∨ ((((True ∧ True) ∨ p5) ∧ p2) → (True ∧ ((p2 ∧ True) ∨ p5))))) ∨ (p3 ∨ p5)) ∨ (False ∧ False)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135509567294293830202735594768 : (((False → ((False ∧ (((p3 → (False → ((False → p1) ∨ False))) ∨ p1) → p2)) → (p2 ∨ p3))) → ((p2 → p4) ∨ True)) ∨ (True ∧ (False ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587615620547241017847785400206 : ((((((((True ∨ ((p3 ∨ ((True ∧ p1) ∧ (p4 ∧ p5))) → p5)) ∨ ((p2 → ((p5 ∧ p4) ∧ p2)) ∨ True)) → p2) → p3) ∨ p4) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117517477207642605832992175942 : ((p2 ∧ ((p5 ∧ ((p4 ∧ (p3 → False)) ∧ (p1 ∨ (p4 ∨ (p5 ∧ ((True ∨ p4) ∧ (True → (p4 → (p5 → p3))))))))) ∨ p4)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113554487562205129065825080545 : ((((True ∧ False) ∧ (((p4 → ((((p5 ∧ (p3 ∧ p3)) ∨ (p5 → (p2 ∨ p2))) ∧ p4) → p4)) → p3) ∨ p1)) ∨ (True ∨ False)) ∨ (p5 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178927763432703007418375243730 : (((p4 → p3) ∧ (((((p1 ∧ p4) ∨ (True ∧ p1)) ∨ p4) ∧ p2) ∨ False)) ∨ (False → ((((((p3 ∨ p1) ∨ p2) → False) ∨ p2) ∨ False) ∧ p4))) := by
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
theorem thm_5_vars_586829706677041141295785174392 : (((((p5 ∧ ((False ∧ (False ∧ (((False → p2) ∧ (p5 → (p3 ∨ p3))) → (((p5 ∧ False) ∧ (p2 ∧ p3)) ∧ True)))) ∧ False)) ∧ p1) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137616806226991487919731344269 : ((False ∨ (((((p4 ∧ (True ∨ p2)) ∧ (p4 → ((p5 ∨ p2) ∨ (False ∧ (p3 → (p3 ∧ p1)))))) ∨ False) ∨ p1) ∨ True)) ∨ ((p2 ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232758809607658577155285617799 : ((p1 ∧ (p5 → True)) → ((p4 ∧ (((p4 → (p4 ∨ p1)) ∧ ((False ∧ p1) ∧ (True → ((False ∧ p4) ∧ (p5 ∧ (True → p3)))))) ∧ p3)) ∨ p1)) := by
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
theorem thm_5_vars_355528985009990495871134838150 : (p5 → ((((p5 ∨ (((p4 ∨ p1) → (((p1 ∨ (p2 ∧ (((p5 → p2) ∨ False) ∨ False))) ∨ p1) ∨ p2)) ∧ True)) → p1) ∧ p5) ∨ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322836551846413447544703290774 : (p5 ∨ (((p2 ∨ (p4 ∨ (((p3 ∨ p1) → False) ∧ (True ∧ p3)))) ∧ (True → ((p5 → p5) ∧ (p1 ∧ (((p4 → p3) ∨ p3) ∧ p1))))) → p1)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h11
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h20 : (p3 ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h21 := h16 h20
      -- False on the left can always be used.
      apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60656843128829639990253442147 : ((True ∧ ((((p4 → False) ∧ p4) ∧ (((p5 ∨ p4) → p4) ∧ (((p4 → True) ∧ False) ∨ (p3 → False)))) ∨ (((False ∧ p4) ∨ True) → True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308442477277463183720997981294 : (p2 ∨ (((False → ((p1 ∨ (p3 ∧ p5)) → (((p4 ∨ ((False ∨ p4) ∧ (False ∨ p1))) ∧ (p2 ∧ ((p5 → p5) ∨ p5))) ∨ p3))) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190134649535668799578307007611 : ((((p2 ∨ p3) ∧ ((p3 → p4) ∨ (True → p5))) ∧ True) ∨ (p4 → ((p3 → p3) → (p3 → ((p2 ∨ (True ∧ ((p1 ∨ p4) → p1))) ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350241609842528376980845139855 : (p4 → (((p5 → p5) → (((True ∧ ((((p3 → True) → p4) → p3) ∧ (True ∧ ((p4 ∧ p1) → p2)))) ∧ p3) ∨ ((p4 ∨ p3) → p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337781205002711529893699822190 : (p1 → ((p3 ∨ ((p1 ∧ ((((p4 → p5) → False) → p3) ∧ p2)) ∨ ((p1 → p2) ∨ p5))) ∨ (((p2 → p3) ∧ p5) → (p2 → (False ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39987055050746743929524257653 : (((p5 → ((((p5 → ((p3 ∨ p5) → ((((False ∨ p4) → ((False ∨ False) → p4)) ∨ p2) ∧ True))) → False) ∧ (p1 ∨ p5)) ∨ p1)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2201759257927871797231558751 : ((p2 ∨ ((p2 → ((p5 → (True → (p1 → ((p3 → p4) ∨ p2)))) → False)) ∧ p4)) ∨ (True ∨ ((p2 → (p2 → p2)) ∧ (p4 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156304846650597600265870929866 : ((p5 ∨ (((p1 ∨ ((p5 → p5) ∨ (p1 ∨ p5))) ∨ (((p2 → p4) ∨ True) ∨ True)) ∨ (p3 ∨ p3))) ∧ ((p4 ∧ (p1 ∧ (p4 → p5))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157197389262200196472421488075 : ((((p1 → (((((False → True) ∧ (False ∧ p1)) ∧ False) → (p2 → p2)) ∨ p3)) ∧ (p5 ∨ True)) → p1) ∨ (((p5 → False) ∨ (False → p3)) ∨ p4)) := by
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
theorem thm_5_vars_171468002023890955688039225195 : (((p1 ∨ ((p3 ∧ (p5 ∨ False)) ∨ ((p3 → p5) ∨ ((p1 ∨ False) ∨ p1)))) ∧ p1) ∨ (p4 → (False → ((((p5 ∧ p4) → p1) ∧ False) → p4)))) := by
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
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261623690546563180597897120332 : ((p5 → p5) → (((p1 → (p3 ∨ (((((((False → p5) ∧ True) → p3) ∧ (p1 ∨ True)) ∧ p2) → (p2 ∨ (p1 ∧ p2))) ∨ False))) → p3) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p1 → (p3 ∨ (((((((False → p5) ∧ True) → p3) ∧ (p1 ∨ True)) ∧ p2) → (p2 ∨ (p1 ∧ p2))) ∨ False))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172962965866736167216207118380 : ((p4 ∧ ((False ∨ (p5 ∨ (((p2 → True) ∧ ((p2 ∨ p2) → p5)) ∨ p4))) → False)) ∨ ((p1 ∨ ((((True → True) ∧ False) ∧ p1) → p2)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311987507038875756648340980347 : (p2 ∨ (p4 ∨ ((((p4 ∨ (p4 ∧ p4)) ∨ p1) → (True ∧ (((False ∧ ((p2 ∨ (p2 ∧ p4)) ∧ True)) ∨ p3) ∨ (p4 ∨ (p1 ∨ True))))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1694707169321787824117548046 : (((((p3 ∨ (True ∧ p4)) → True) → ((p4 → p1) ∨ ((p3 ∧ (p5 ∧ (p2 ∧ p5))) ∨ (False → p2)))) ∧ True) ∧ (p5 ∨ (p2 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65049625543338123260444726680 : ((p2 ∨ (p1 ∧ (((p5 ∧ ((p4 → p3) ∨ (True ∧ p1))) → ((p3 ∨ p1) ∧ (((False → p5) ∧ ((p3 ∨ p1) ∨ p3)) → p3))) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246105903137043083301670413501 : ((p4 ∧ p1) ∨ ((True → p2) ∨ (p2 → ((((p5 ∧ ((p4 ∧ (False → (p3 ∧ p4))) ∧ p5)) ∧ p1) ∨ (p4 ∧ p5)) ∨ ((p2 ∨ p3) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177931376260845081623141159322 : (((((False ∧ p4) ∧ (p5 ∧ False)) ∨ (((p1 → p5) ∨ p3) → p4)) ∨ p5) ∨ ((p1 → (((((p3 ∨ p3) ∧ p1) → False) ∧ p1) ∨ True)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617534707467100683299869114138 : ((((((p2 → p4) ∧ (True → (p4 → p4))) ∧ ((True ∨ ((p1 → p1) ∧ ((True → True) → (p1 ∨ (p4 → (False ∧ p2)))))) → p2)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_729664526938475856034501122096 : (((((False → p2) ∨ p4) → (p5 → ((((p1 → p2) → ((p4 ∨ p4) → (False ∧ False))) ∨ (False ∨ False)) ∨ ((p4 ∧ (p4 ∧ p2)) → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801980365859096607176235434969 : (((p2 → ((p5 → False) ∨ ((p1 → (p3 ∧ ((p3 ∧ (p4 ∨ False)) ∧ p1))) → (p2 → (p4 → (((p5 ∨ p4) → False) → (True → p1))))))) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : (p5 ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41102108811922158238304187652 : (((((p2 ∨ (True ∨ ((p4 → True) ∨ (True → False)))) → (((p4 → True) → False) ∨ ((p1 ∧ p2) ∨ p4))) ∧ (p4 → (p5 ∧ p5))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148634386083100645020970600841 : (((p1 → (((False → ((p5 → False) → p5)) ∧ p2) ∧ True)) → (((p2 → ((p5 ∧ True) ∨ p2)) ∨ p3) → p2)) ∨ (True ∧ (True ∨ (p4 ∨ False)))) := by
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
theorem thm_5_vars_112122769291464882463019820621 : (((True ∧ (((False ∨ (p3 ∧ p4)) → ((((p2 ∨ p2) ∧ p4) → True) ∧ p5)) → (p5 ∨ (((p2 ∧ True) → p4) ∧ p4)))) ∨ True) ∨ (p5 → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78623237709411761169598264381 : (((((False ∨ (p2 → p4)) → ((((True ∧ p4) ∨ (p3 ∨ False)) ∨ p3) → ((False ∨ True) ∧ (p1 ∨ p2)))) → (False ∧ True)) ∧ (p2 ∧ p3)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : ((False ∨ (p2 → p4)) → ((((True ∧ p4) ∨ (p3 ∨ False)) ∨ p3) → ((False ∨ True) ∧ (p1 ∨ p2)))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h17 =>
            -- False on the left can always be used.
            apply False.elim h17
          case inr h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h19 =>
          -- False on the left can always be used.
          apply False.elim h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h21 =>
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h27 =>
          -- False on the left can always be used.
          apply False.elim h27
        case inr h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h31 =>
            -- False on the left can always be used.
            apply False.elim h31
          case inr h32 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h4
        case inr h33 =>
          -- False on the left can always be used.
          apply False.elim h33
    case inr h34 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h35 =>
        -- False on the left can always be used.
        apply False.elim h35
      case inr h36 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h37 := h2 h6
  -- We need to get the left conjuct of h37 based on <expert-advice>.
  let h38 := h37.left
  -- False on the left can always be used.
  apply False.elim h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323785353968491168376502970489 : (p5 ∨ ((((((False → (p4 ∨ (p4 ∨ True))) ∨ (p2 ∧ p4)) → p1) ∧ ((p3 ∧ p3) → p3)) → p1) ∨ (p5 → (p3 ∧ (True → (p1 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((False → (p4 ∨ (p4 ∨ True))) ∨ (p2 ∧ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104761940644997016931650029335 : ((((((((p5 ∧ (False → p2)) ∧ ((p3 ∧ p4) ∨ p5)) ∧ p4) ∧ (p1 ∨ (p3 → p5))) ∨ (p4 → True)) → False) → (True → p5)) ∧ (True ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((((p5 ∧ (False → p2)) ∧ ((p3 ∧ p4) ∨ p5)) ∧ p4) ∧ (p1 ∨ (p3 → p5))) ∨ (p4 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47998577210154891011380819237 : ((((((((False → p4) → p2) ∨ p1) ∨ p4) ∨ ((p2 → p1) → (False ∧ p4))) ∨ ((p2 ∧ (True → (p4 ∧ p5))) ∧ p4)) → (p5 ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
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
      case inr h7 =>
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
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349997127484383524782551757045 : (p4 → ((((((False ∧ True) ∧ p5) → p1) → (p1 ∨ (((p5 ∧ False) ∨ ((p1 ∧ False) → ((p2 ∨ p2) ∧ p3))) ∧ (p1 → p2)))) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618339243854023703093512979857 : (((((p4 ∧ ((False ∨ False) ∧ p4)) ∨ (False ∨ (False → (True ∨ (False ∨ (((False → p2) → (p1 ∨ p4)) → (p3 ∧ (p4 ∨ p1)))))))) ∨ p3) ∨ p2) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111731830630103700497544374843 : (((((p3 → p1) → ((p1 ∧ p1) ∨ (p3 ∨ ((((p5 → (p4 → ((p2 ∨ p1) ∨ True))) ∧ p5) ∨ True) ∨ p4)))) → False) ∨ p2) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342615048131854475526661009881 : (p2 → ((p4 ∨ (((p4 ∧ (False → p3)) → (False → (p1 → p2))) ∨ p5)) → ((((False → False) ∧ p5) → p2) → (p3 → ((p1 → p5) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186438897677546018942831559646 : (((p3 → (p4 ∨ (((p1 ∧ (False ∧ False)) ∨ p1) → p4))) → p4) → (((p4 ∨ p4) ∧ ((p5 → p2) → p5)) ∨ (False → ((p5 ∧ p3) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146727510934739802063940873678 : ((p2 → ((((p3 ∨ (((p1 ∨ False) ∧ p5) ∧ False)) ∧ (p3 ∨ ((p3 ∨ False) ∨ p5))) ∨ p2) ∧ (False → p4))) ∧ (p1 ∨ (True ∨ (p3 → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244437927093150585793801265730 : ((False ∧ p2) ∨ ((((((p3 → (p5 ∧ (True ∨ p1))) → p3) ∨ ((False ∧ (p4 ∨ p1)) ∨ p3)) ∨ p4) ∧ (p2 ∧ ((p1 → p1) → False))) → False)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h3.left
      let h7 := h3.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : (p1 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h10 := h7 h8
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- False on the left can always be used.
        apply False.elim h13
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h3.left
        let h17 := h3.right
        -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
        have h18 : (p1 → p1) := by
          -- Implications on the right can always be decomposed.
          intro h19
          -- One of the premise coincides with the conclusion.
          exact h19
        -- We have shown the premise of h17, we can now drive its conclusion.
        let h20 := h17 h18
        -- False on the left can always be used.
        apply False.elim h20
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h3.left
    let h23 := h3.right
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h24 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h25
      -- One of the premise coincides with the conclusion.
      exact h25
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h26 := h23 h24
    -- False on the left can always be used.
    apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308708116714501450868009349627 : (p2 ∨ ((p5 ∨ ((((p5 ∧ (p5 → False)) ∧ (p3 ∧ ((p5 → p1) ∨ p1))) → (((((p5 → p3) → p2) → p5) ∨ p5) ∧ p2)) ∨ p5)) ∨ p1)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h11.left
  let h15 := h11.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h17 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h18 := h13 h17
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h20 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h21 := h13 h20
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787987606607147726455539274810 : (((p4 ∨ (p5 → (((True ∧ (p4 ∧ True)) ∧ ((False ∧ True) → (p1 ∨ (False → p1)))) ∨ (p4 ∨ ((p2 ∧ p2) ∨ (p5 → (p5 ∧ p2))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164846463359182804386066121337 : (((p4 ∧ (p2 ∧ (False ∧ ((p3 ∨ ((p3 ∨ False) ∨ p4)) → ((True → p5) ∨ p4))))) ∨ p5) ∨ ((p5 → ((p1 → (p1 ∨ p3)) ∨ p1)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664845165334919491900488345135 : ((((p2 → (((p1 ∨ False) ∨ ((((p2 ∨ (p2 → True)) ∨ True) → (((p1 ∨ p1) ∨ p4) ∨ (p4 ∨ p5))) ∧ p3)) → p4)) → (p4 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133670738718386889883022419547 : (((((p2 ∧ (p2 ∧ ((p2 → p4) ∨ ((p3 → p3) → (p1 ∨ p3))))) ∨ ((p5 ∧ p5) ∨ False)) → (p5 ∧ p2)) ∧ p2) ∨ (p5 → (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158572359126210998617003871362 : ((True ∧ ((p2 ∨ ((True → p4) → (p2 ∨ (False ∨ p1)))) → ((True ∨ (p5 ∨ (p4 ∧ p4))) → p2))) ∨ (((p3 → p3) → True) → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225724686362777237910471866676 : (((p4 → False) ∧ True) ∨ ((p2 → p2) ∧ ((((True ∨ ((False → (p2 → p1)) ∧ (p5 ∨ (p3 ∨ (p5 ∧ False))))) ∧ (p4 ∧ True)) → p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607802379625994365241318859774 : (((((p3 ∨ (((False ∨ True) ∧ p4) ∨ (p2 → (((p3 ∨ p3) ∨ ((p1 → ((p1 ∨ (False → p5)) ∧ False)) ∨ p1)) ∧ p2)))) ∧ p5) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53605547382586811755181728858 : ((((False ∧ ((True ∨ False) → (p1 ∧ p5))) ∧ (False ∧ p1)) ∧ (((((p4 → True) → (True ∧ p1)) ∨ p2) ∧ ((p1 ∨ p3) ∧ False)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695338079474285410384183801944 : (((((p5 ∧ (((p4 → (p1 ∧ ((p1 → p4) → True))) → True) ∧ p1)) → p3) → (((p4 ∨ (False ∧ False)) → True) ∧ (p5 ∧ (p5 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66626287140303441015020543288 : ((True → (((((False ∧ p2) ∨ (True → (p5 ∨ p4))) → (p3 ∨ (False ∨ p1))) → p3) ∧ (p5 → ((p3 ∧ (p5 ∨ (True ∧ False))) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319466259680398050207313610490 : (p4 ∨ ((p1 ∧ ((((p5 ∧ (p4 ∨ p4)) ∧ (p1 ∨ p3)) → p3) ∨ p1)) ∨ (True → (p3 → (p4 ∨ ((p3 ∨ p5) ∧ (p4 → (p3 ∨ p2)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58917662482094284599037838176 : (((p1 ∧ p1) ∨ (((p5 → False) → ((((p3 ∨ p3) ∧ p5) ∧ (((p5 ∧ True) ∨ True) ∧ ((p4 ∨ (True ∨ p1)) ∧ p3))) ∨ p2)) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50879268370713261628899615922 : (((((((True → (p4 ∨ ((p5 ∨ p3) → p1))) ∧ True) ∨ (p4 → (p3 → False))) → p1) → p4) ∧ (p5 ∨ (p4 → (p2 → (p1 ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178357989529250247822452914924 : (((p5 ∨ (p2 ∧ (p5 ∨ (True → (True → (p2 ∧ True)))))) ∨ (p4 ∧ p5)) ∨ ((True ∧ p4) → ((p5 → p3) ∨ (p1 ∨ ((p2 ∧ p2) ∨ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789758052337063777147651408035 : (((p5 ∨ ((p3 ∨ ((p5 ∧ True) ∧ False)) ∨ ((p4 ∨ (p1 ∨ (((p3 ∨ ((p5 ∧ p4) ∨ p1)) → ((p3 → False) → p3)) ∧ False))) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157116909104519749804487911646 : (((((p4 ∨ ((False ∧ (((True ∨ (True ∨ p5)) → (False ∨ p1)) → False)) → p3)) ∧ p2) ∧ p2) → p4) ∨ ((p5 ∨ (True → (p5 ∧ p3))) → p5)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- One of the premise coincides with the conclusion.
    exact h6



