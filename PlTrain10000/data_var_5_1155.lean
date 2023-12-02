variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696960878463827297112625775411 : ((((((p5 ∨ p3) ∧ ((p5 ∨ (p4 ∨ False)) ∨ True)) → (p2 → p2)) ∧ ((p5 ∧ (True ∧ (((p3 ∨ False) ∨ False) ∨ (p5 ∧ p1)))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718983982581992332152642426277 : (((((p5 ∨ p2) → (True ∧ p1)) ∨ (((p2 → p1) ∧ (p2 → (p2 → (p5 ∧ (((p4 ∧ p4) ∧ p4) ∨ True))))) ∧ (True → (p5 ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327084780300010334328623117907 : (True → (((p4 ∧ (p2 ∧ p4)) ∨ (((p2 ∨ (p2 ∧ (p2 ∧ True))) ∧ (False → (True ∧ (False → True)))) ∧ (p3 ∧ (p2 ∧ (p1 ∧ p2))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698942619487966991987362886492 : ((((p4 ∧ ((True ∨ p1) ∧ (p3 ∧ (((True ∨ True) ∧ p5) ∨ p2)))) ∨ ((((p2 → ((p2 ∧ False) → False)) → (False ∧ p3)) ∧ True) → p2)) ∨ p4) ∧ True) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → ((p2 ∧ False) → False)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h4
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157222041289152830745165432637 : (((((p1 ∨ ((((p4 ∧ p1) ∨ False) ∨ p4) ∧ (p2 → p5))) ∧ p3) → ((False ∨ p5) ∧ p4)) → p2) ∨ (((p3 → p3) ∨ p1) → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168280266583532040903711708399 : (((p2 ∧ p5) ∧ ((False → (p5 ∧ ((p5 ∧ (p2 ∨ p2)) ∨ ((p2 → True) ∨ True)))) ∨ p1)) → ((((False → p5) → (p3 → False)) → p3) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231899608697466985869753538366 : (((False ∨ True) → False) → ((p2 ∧ (p2 ∨ (p4 ∨ True))) ∨ (p4 → (False ∧ ((p1 → (p5 → p1)) ∨ (((p3 ∨ p5) ∧ p5) ∨ (p5 → False))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787754084898302781351484258510 : (((p4 ∨ (True → ((p5 ∨ ((p2 ∨ (True ∧ True)) ∨ p1)) ∧ (((p3 ∨ False) ∨ False) ∨ (p5 ∨ (True → (p5 ∨ (p5 ∨ (p3 ∧ p1))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661494137571944830571482134378 : (((((p4 ∧ ((((p3 ∧ (((p1 → (p4 ∧ p4)) → False) ∧ p5)) ∧ (True → True)) ∧ True) ∧ p2)) ∧ (False → (p1 ∧ p5))) → (p1 ∧ p4)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h13.left
  let h15 := h13.right
  -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
  have h16 : (p1 → (p4 ∧ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h14, we can now drive its conclusion.
  let h18 := h14 h16
  -- False on the left can always be used.
  apply False.elim h18
  -- Conjunctions on the left can always be decomposed.
  let h19 := h1.left
  let h20 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h19.left
  let h22 := h19.right
  -- Conjunctions on the left can always be decomposed.
  let h23 := h22.left
  let h24 := h22.right
  -- Conjunctions on the left can always be decomposed.
  let h25 := h23.left
  let h26 := h23.right
  -- Conjunctions on the left can always be decomposed.
  let h27 := h25.left
  let h28 := h25.right
  -- Conjunctions on the left can always be decomposed.
  let h29 := h27.left
  let h30 := h27.right
  -- Conjunctions on the left can always be decomposed.
  let h31 := h30.left
  let h32 := h30.right
  -- One of the premise coincides with the conclusion.
  exact h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25458107487284963092519229865 : (((p3 ∧ (p4 ∨ p3)) → ((((((True ∨ False) ∨ (p4 ∧ p4)) → (p5 ∧ (p3 ∨ True))) ∨ ((p1 ∨ False) ∧ p4)) ∨ (p1 → True)) ∨ False)) ∧ True) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112652416426623924826085331123 : (((((p4 → (((p5 ∨ p5) → True) → p4)) ∨ (((p3 ∧ (False ∧ p4)) ∨ (p4 → p3)) ∧ True)) ∧ (p4 ∧ (p5 → p5))) → False) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321559377245016944024872207173 : (p4 ∨ (p2 → (((p2 → p5) ∧ ((p4 ∧ (p5 → (p5 → p5))) → p4)) ∨ ((((((p4 ∨ (p4 ∨ False)) ∧ True) ∨ p4) ∧ p2) ∨ p1) ∨ True)))) := by
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
theorem thm_5_vars_3420494379243438260274940534 : (True ∧ ((p5 → (False ∧ ((p4 ∧ (p5 ∨ False)) ∨ ((True ∨ ((p5 ∨ ((p1 ∧ (p4 ∨ p4)) → (p1 ∧ True))) → p5)) ∧ False)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227771034755691108352772141978 : ((p1 ∧ (False → True)) ∨ ((p3 ∨ (((p5 ∧ True) → p2) → ((p1 ∧ (p4 → (p1 ∧ (((p4 ∧ p3) → p2) → True)))) ∨ (p2 ∨ True)))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_67760701235914369846464316515 : ((p2 → ((((p5 ∨ p4) ∧ (p4 ∨ (p3 ∨ (p4 ∨ (p5 → (p3 ∧ (p4 → (p4 → (p3 ∧ p2))))))))) ∧ ((p5 ∨ p3) → p2)) ∨ p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322289751014487247240861945347 : (p5 ∨ ((((True → (((p4 → p4) → p4) ∧ (((p5 → p3) → (p2 ∧ (p4 ∨ (p4 ∧ p2)))) ∧ True))) ∧ (False → (p1 ∧ p1))) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49306053207295203325347897920 : (((p1 ∨ ((((True → p3) ∨ ((False ∨ False) → False)) ∧ (p4 ∧ ((False ∨ False) ∧ (p3 ∧ p4)))) ∨ (p4 → True))) ∨ ((p1 → True) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695755433256412952173471136514 : (((((p5 ∧ (p3 → p3)) ∧ ((((p3 → p5) ∨ p1) → (p5 → p4)) → False)) → ((p1 ∧ p1) → ((p2 ∨ ((p1 → p3) ∨ p2)) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2546863025855655644144500641 : (((((p1 ∧ False) → (p3 ∧ p3)) ∧ p2) → False) ∨ (((p4 ∨ p3) ∨ ((p3 ∧ (True ∨ (p1 → p4))) ∨ True)) ∨ (p3 → (True ∨ False)))) := by
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
theorem thm_5_vars_759988490002781222874149962832 : (((p2 ∧ (((True ∨ p4) ∧ (p5 ∧ False)) ∨ ((p3 ∧ (False → True)) ∧ ((p4 → (p3 ∧ ((((p5 ∧ p4) → False) ∧ p5) → False))) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49321406988781458366645307393 : (((p3 ∨ (p4 ∧ ((p4 ∨ p3) ∨ (p5 ∧ ((p3 ∨ True) → ((True ∨ (p3 → ((False ∧ p4) → False))) ∨ p4)))))) ∨ (p2 ∧ (p3 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323237940262771029827020584720 : (p5 ∨ (((p5 ∧ (p5 ∨ False)) ∨ ((p3 ∧ ((True ∨ p2) ∧ (p4 ∨ True))) ∨ (((p5 ∧ (p4 → (p5 ∧ False))) → p4) → p5))) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316535741257663109328796804561 : (p3 ∨ (p2 ∨ (True → (((True ∧ p1) → (p4 ∨ p4)) ∨ (p2 → (p4 → (p4 → (p2 ∧ ((((p3 ∨ (p4 → p1)) ∨ p2) ∨ p1) ∨ False))))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731118677484991560965217233188 : ((((p2 ∨ (True ∧ p3)) → (True ∧ (p5 ∨ ((p1 ∨ p1) ∨ (False ∨ (p1 → ((p3 ∧ (p4 ∧ (p3 ∧ p1))) ∨ (p5 ∨ (False ∨ False))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58944211073488978710052218842 : (((p1 ∧ p5) ∨ (p4 ∨ ((((p5 → (p2 ∨ (((p2 ∧ (p1 ∧ False)) ∧ ((True ∧ (p3 ∨ p5)) → p3)) → p3))) ∨ p3) → p5) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112211289880150680361109303898 : (((False ∨ (((((p1 ∧ (p2 ∧ p5)) → False) ∨ p2) ∨ False) ∧ ((True ∧ ((((p2 ∨ p2) ∨ p3) → p3) → p1)) ∧ p3))) ∨ True) ∨ (p4 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349270934198505096580618719221 : (p3 → (p2 → ((p2 ∧ ((True → True) → (p2 → (p5 ∨ ((((True → (((p5 ∨ (p5 ∧ p1)) → p4) ∨ p1)) → p5) ∨ False) ∨ p2))))) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256273022489403767350227082869 : ((False ∨ p1) → ((((p4 ∧ (p4 ∨ ((p3 ∧ p4) → (p2 ∧ (True ∨ (p1 → ((True ∨ (p2 ∨ False)) ∧ p5))))))) → (p1 → p3)) ∨ True) ∨ True)) := by
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
theorem thm_5_vars_320082027241869136023107603391 : (p4 ∨ (((p4 ∨ p1) ∧ p3) → (((((True ∧ (p2 ∧ p2)) ∧ (p3 ∨ True)) → (p1 → p5)) → (((p5 ∧ True) → p3) → (p5 ∨ p2))) ∨ p3))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216505328508343212059992532105 : ((p5 → ((p4 → False) → False)) ∨ ((p3 ∧ ((((False → False) ∨ True) ∧ (p1 ∧ p3)) ∨ (p4 ∨ p2))) ∨ ((p1 ∧ (p5 ∧ p4)) → (p3 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59289668376535584531394731126 : (((p3 ∨ p4) ∨ ((((((p5 → p3) ∨ p1) → (p5 → (p2 ∨ p1))) ∧ (p2 ∧ (True ∧ False))) ∨ ((p4 ∨ True) ∨ False)) ∨ (p3 ∧ p5))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64844533406449808914431285526 : ((p2 ∨ ((p4 ∨ (((((False → (p5 → ((False ∨ ((p3 ∧ False) → (p1 ∨ p2))) ∨ (p4 ∨ p2)))) → p1) → p4) ∨ p4) → p4)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159891864194581831394827739045 : (((((p5 ∨ (p3 ∧ ((((True ∨ (p4 ∧ p5)) ∨ p4) → p1) → (p1 ∧ p4)))) ∨ True) ∨ True) → False) → ((p5 ∧ p5) ∨ ((p3 → p1) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ (p3 ∧ ((((True ∨ (p4 ∧ p5)) ∨ p4) → p1) → (p1 ∧ p4)))) ∨ True) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157966564396732569576986718304 : ((((p2 ∧ p4) ∧ (((p5 → p2) ∨ p2) → p3)) ∨ (p5 ∨ ((p3 → (p4 → p2)) ∧ (p4 ∨ True)))) ∨ (((p1 → p1) ∨ p5) ∧ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53119472355202265224179157799 : (((p4 → ((((p5 ∨ p3) ∧ p1) ∧ p4) ∧ ((p1 ∧ p5) → p4))) ∧ (p3 → ((p2 → p4) → (p4 ∨ ((False → p4) → (p2 → p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628627039814893612300564131102 : (((((p3 ∨ (((p3 ∧ (p5 ∧ p5)) ∧ ((((p5 ∧ p1) ∧ False) → p1) → (p1 ∨ (False → True)))) ∨ (True ∧ (p4 ∧ p3)))) ∧ True) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157470980165803138857736908997 : ((((((p5 ∧ p5) ∨ (p3 ∧ p1)) → (p1 ∨ (p4 ∧ (p1 ∨ (False ∨ p4))))) → p3) ∨ (False → True)) ∨ ((((True ∨ p4) → False) ∧ p2) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150055188140870755940156983583 : ((True → (((p3 ∧ ((p3 → False) ∨ ((p2 → (p2 → ((p5 ∧ False) → False))) → (p1 → p5)))) ∨ True) → False)) ∨ (((p2 → False) ∧ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41883628406262800330548420413 : ((((p1 ∨ (p5 ∧ False)) ∨ ((p1 ∧ True) → ((((p1 ∨ p1) → p1) → (((p3 ∧ ((p5 ∨ p4) ∧ False)) ∧ p4) ∨ p2)) ∨ p3))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4581684531845281535408549415 : (p4 → (((False ∧ ((p1 ∨ (p4 ∨ ((False ∨ p5) ∧ p3))) ∧ ((p4 → (((p3 ∧ p1) → p5) ∨ False)) ∧ p1))) ∧ p3) ∨ (True ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348243300369440865113985998725 : (p3 → (True ∧ ((((p2 → p4) → p2) ∨ ((((((((p1 → (p2 → False)) ∧ p5) ∧ True) → (False ∨ p5)) ∨ False) → False) ∨ p3) ∨ True)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351533047762298694656207726249 : (p4 → (((((p2 ∨ False) → p3) ∧ (p4 → (p3 → False))) ∨ (True ∧ (p5 ∧ ((p1 ∧ False) ∨ p1)))) ∨ (True ∨ ((True → p2) ∧ (p1 → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258784988746674314904052486715 : ((True → False) → (((((p3 ∧ p1) ∧ p3) ∧ (False ∧ False)) ∨ (False ∧ ((p1 → p3) → True))) ∨ (p1 → (p2 ∨ (((p3 ∨ p3) ∨ p2) → False))))) := by
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
theorem thm_5_vars_151214430893245881499893829518 : ((((((p1 ∨ False) ∧ p5) → p3) → (((False → (p4 → (p2 ∧ (p5 ∧ (True ∨ True))))) ∨ p1) ∧ p5)) → p3) → (p2 ∨ ((p5 ∧ p4) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317958428254466119898460051587 : (p4 ∨ ((p5 ∨ (p4 ∨ ((p5 → True) → (p1 → (p5 ∨ ((((True → p2) ∨ (True → (p5 → (p1 → True)))) ∨ (p3 ∧ p4)) ∧ True)))))) ∨ False)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112752363542714132809492966430 : ((((p3 → ((p4 ∧ (p1 → (((p1 ∨ p3) → p4) ∧ p3))) ∧ p1)) → ((((p2 → False) ∨ (p5 ∨ p4)) → True) ∨ p2)) → p3) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61405632265614290733489444454 : ((p1 ∧ ((True → (True ∧ ((((p3 ∧ ((p2 ∨ (p1 → p2)) ∧ (p1 ∧ (p4 → p5)))) ∨ (False ∧ (p1 ∨ True))) → True) → p5))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51686824399502256186694140760 : ((((p1 ∨ (p4 → ((p2 → ((p5 → False) → False)) ∧ (p2 ∧ True)))) ∨ (False → p5)) ∧ ((p4 ∨ (True ∨ p4)) ∧ (p2 ∨ (p4 ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69270363080940056202858687017 : ((p5 → ((p5 ∧ False) ∨ (((((((p5 ∧ (True ∧ (False → p1))) ∨ ((True ∨ False) ∧ (True ∨ p5))) ∨ True) ∨ p3) ∨ p5) ∨ p3) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49088866076544173840544652273 : (((((p4 ∨ p3) ∨ (True ∧ (True ∧ (((False ∨ ((p3 ∧ p1) → True)) ∧ True) → p4)))) ∧ ((p4 ∨ p2) → False)) ∨ (p1 → (p5 → p1))) ∨ p1) := by
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
theorem thm_5_vars_617450101342870043789479523207 : (((((((p1 → False) ∨ (p3 ∨ p1)) ∧ p5) ∧ ((((((p4 ∨ p3) ∧ ((True ∨ True) ∨ p2)) → False) ∧ p1) → (p1 ∨ p5)) ∧ p3)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_111657475449858990914664204485 : ((((p1 ∧ (((((p3 ∧ ((True ∧ (p3 ∨ False)) ∨ p3)) ∧ p3) ∨ p2) ∧ p2) → ((p3 ∨ (p1 ∧ False)) ∧ p3))) ∨ p5) ∨ p3) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764448926288418069654158283696 : (((p4 ∧ ((p5 ∨ ((p1 ∧ (p2 ∧ (p4 → ((True → ((False → (p3 ∨ (((False ∧ p2) ∨ p3) → False))) ∨ True)) → p4)))) ∨ p3)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45349573085446264495735434427 : (((p4 ∧ (((p5 ∨ p5) ∨ ((((p5 → (p4 ∨ p3)) ∨ ((False ∧ ((False → p1) → p3)) ∧ True)) → True) → (p5 → p1))) ∨ False)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232129137095597321533854217102 : (((p5 ∨ p5) → True) → (((((True ∨ False) → ((p1 ∧ (p1 → (((True → p1) ∧ p4) ∨ (True ∧ p3)))) → p3)) → p1) → p3) ∨ (True ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180415752614304482037724146815 : ((((((p1 ∧ True) ∨ p4) ∧ (p3 → (True ∨ p5))) ∧ p3) → (p2 ∨ p5)) → (((p5 → (((p3 → False) ∨ (p5 ∨ p2)) ∨ p2)) ∨ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41716949592341596887107279955 : ((((((p5 ∨ p1) → p2) ∧ p2) ∧ (((p3 → False) ∧ p3) ∨ (((((p4 ∧ True) → p1) → ((False ∨ p3) ∧ p3)) → p1) ∨ True))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303709519305090979113979557724 : (p1 ∨ ((((((False ∧ (p2 ∧ (p2 ∨ (p5 ∧ False)))) ∨ (False ∨ (True → p4))) ∨ ((p5 → (p5 ∧ p5)) ∨ (p4 → False))) ∨ False) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251670937578737109260117322204 : ((p3 → p2) ∨ ((p5 ∧ ((((True → p3) ∨ ((p2 ∨ p3) ∧ False)) ∧ ((p2 ∧ p1) ∧ (p2 ∨ (p1 ∨ p1)))) ∧ (False ∧ p1))) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_993418466017842595339793613723 : (((p4 ∧ (p5 ∨ ((p2 → p5) ∧ (p3 ∧ ((True → p5) ∧ ((p4 → p3) ∧ ((((False ∧ p5) → p2) ∨ False) ∨ ((True ∨ p4) → p1)))))))) → p5) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h17 := h10 h16
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- False on the left can always be used.
        apply False.elim h18
    case inr h19 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h20 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h21 := h10 h20
      -- One of the premise coincides with the conclusion.
      exact h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_13718966766865962949440419879 : (((((((False ∧ False) → p1) → (((False ∨ p5) ∨ False) ∨ ((p5 → (True ∨ p1)) → p2))) ∨ (p1 → (p4 ∨ p3))) ∨ True) ∧ (True ∨ p5)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348868951827924399501920905457 : (p3 → (p2 ∨ (((p3 ∧ (((p3 → True) ∧ True) → False)) ∧ ((((True → False) ∧ p2) → p4) ∨ p5)) → (((p4 ∧ True) ∧ (p5 → p4)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : ((p3 → True) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h8
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h12 : ((p3 → True) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h14 := h6 h12
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94722993777259371029463828664 : ((p3 ∧ (((((True ∧ False) ∨ p1) ∨ p2) → (((p2 ∧ (False ∨ p3)) ∧ (p1 ∧ p1)) ∨ (p2 ∨ p3))) → (p2 ∧ (p5 ∧ (p1 ∨ p2))))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((True ∧ False) ∨ p1) ∨ p2) → (((p2 ∧ (False ∨ p3)) ∧ (p1 ∧ p1)) ∨ (p2 ∨ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h12 := h3 h4
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111745451732676239799558265670 : ((((p4 ∨ (p3 ∨ (((p4 ∨ p1) → (True ∧ ((p4 ∨ (p5 ∨ p3)) ∨ p5))) ∧ (p2 → ((False ∨ True) ∧ p1))))) → False) ∨ True) ∨ (p5 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190664190570815502168362480480 : (((True → ((True ∧ p2) → (p2 ∧ (False → p3)))) → False) ∨ ((p4 ∨ True) ∨ ((p4 ∧ (((p1 ∨ p5) ∧ (p1 ∧ (False → p1))) ∧ p4)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117599169909256916893256004342 : ((p2 ∧ (p2 ∨ (((p3 ∧ ((p1 ∧ True) → p3)) ∨ p3) ∧ (((False → (True ∨ (True → p5))) ∨ p5) ∨ ((p4 ∧ p1) → p4))))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178234806979436374583997969976 : (((p4 → ((p3 ∨ p3) ∨ ((((p2 ∨ p2) ∧ False) → p4) ∧ p1))) → p4) ∨ ((True → p3) → ((p5 → p5) ∨ ((p3 ∨ (p4 ∧ False)) ∨ True)))) := by
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
theorem thm_5_vars_180850094781621121708730003548 : ((((True ∧ p2) → p3) ∨ (p2 ∧ (p5 → ((p5 → p3) ∨ (p4 ∨ p1))))) → (((p4 → (p1 ∧ ((False ∨ p4) ∧ p2))) ∧ (p2 ∨ p4)) → p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345514988152358252466342057083 : (p3 → (((p2 → ((p5 ∧ p1) → (True → (False ∨ (((p5 ∨ p1) ∧ p5) → p3))))) → (((p3 → True) ∧ p1) ∨ (p2 ∧ (p3 ∨ False)))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41110669980983601069808722444 : (((((p2 → p2) → ((p2 → (p5 ∨ p3)) ∨ ((True ∨ (p2 → False)) ∨ (p2 ∨ (p1 ∨ (p4 ∨ p3)))))) ∧ ((p3 ∧ p2) ∨ True)) ∨ p5) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343532811435883837888756369017 : (p2 → ((True ∨ True) → ((((True → (p2 → (p5 ∨ (p3 ∧ p3)))) ∧ (True ∧ p4)) ∧ p3) ∨ (((p1 → (p5 ∨ p4)) ∨ True) ∨ (p4 → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206058235746963021410315351171 : ((p3 ∧ ((p3 ∧ (p4 ∧ p2)) ∧ p3)) ∨ (((p2 ∧ ((((p5 ∨ (p2 ∨ p3)) → (p4 ∧ p3)) ∧ False) → (True ∧ True))) → p4) → (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64963076439736561644636120522 : ((p2 ∨ ((((False → (p3 ∧ p1)) ∧ False) → p2) ∧ ((p5 ∨ p5) ∨ (((p1 → ((p1 → p2) ∨ (p4 ∨ (True → False)))) → False) ∨ True)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191799778850998216851501859355 : ((p2 ∨ ((((p4 → p1) ∨ False) → (p4 ∧ p1)) → False)) ∨ (((p5 → True) ∧ (p2 → (((p5 ∨ True) ∧ p5) ∧ False))) → ((p1 → True) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586336133001727590915566283878 : (((((((((False ∨ p3) → True) ∧ p5) ∧ p4) ∨ ((p2 ∨ ((True → (True ∨ ((True ∧ p3) ∨ (False ∨ p4)))) → p4)) ∧ p5)) ∧ p3) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309632826471083779477007896294 : (p2 ∨ (((((p3 → True) ∨ (False ∧ p4)) → False) ∧ ((p1 → ((p4 ∨ (((p4 ∨ p2) ∧ p4) ∧ True)) → p1)) → p4)) ∨ (True ∨ (True ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133774269523125084481474027132 : (((((p3 ∧ (p4 → p1)) → p5) ∨ ((((True ∧ True) → (p2 ∧ (p5 ∧ p4))) ∨ (p3 → p5)) ∨ (True ∧ p3))) ∧ p4) ∨ (p5 → (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768305685948906579261310611193 : (((p5 ∧ (((p4 → (p3 ∨ p2)) ∧ (p3 → ((True ∨ False) → (p2 ∧ (((False ∨ (True ∧ p4)) → True) ∧ True))))) ∨ ((p4 ∧ True) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156980364638448898639432208450 : ((((p2 ∨ ((True ∧ p3) ∨ ((p4 → False) ∧ p4))) ∨ (p1 ∧ (p4 → (p4 → (p2 ∨ True))))) ∨ True) ∨ (((p1 → p2) ∨ (p1 → p1)) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355489725636555157872837824014 : (p5 → (((p5 → p2) ∨ (((((((p2 ∧ (False → p1)) → p3) → p5) → (p3 ∧ (p1 ∨ p1))) ∧ p3) ∨ True) ∨ (False → False))) ∧ (p3 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312037823032702861455291523152 : (p2 ∨ (p4 ∨ (p4 → ((((p4 ∨ p2) ∨ (p2 ∨ p2)) → ((p1 → ((p1 → p5) → p1)) ∧ (False ∨ (((False ∧ p1) ∨ True) ∨ p4)))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241518499190116587753891749312 : ((False → p3) ∧ (((p4 ∨ (p4 → p1)) ∨ ((((p3 ∨ ((p2 ∨ p1) → p3)) → (p2 ∨ p3)) → p2) → ((p1 ∨ p4) → (p4 → p2)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50127581744177842106148042628 : (((p3 ∨ (p2 ∧ (((p3 → (False ∧ ((((p1 ∧ p1) → p4) → True) → p4))) → p1) ∨ (p2 ∧ p4)))) ∧ (((False ∧ p2) ∨ p2) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53052510710944964160476424477 : ((((True → p4) ∨ (((p1 ∨ (p1 → p2)) → (p1 ∨ p5)) ∧ p5)) ∧ ((p2 → (((p1 ∧ ((False ∧ False) ∨ False)) → p1) ∧ True)) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792639613081981164285321233145 : (((True → (((False ∧ True) ∧ (p1 → (p4 ∨ True))) ∨ ((p1 ∧ ((p3 → ((True → p5) ∨ ((p5 ∨ (False ∨ True)) → False))) ∧ False)) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77388701752332556478302962144 : ((((p1 ∨ p2) ∨ (p1 ∨ ((p5 ∧ ((False ∨ p1) ∨ p1)) → (((True → ((p1 ∧ p2) ∧ p1)) → (False ∨ p3)) ∨ (p3 → p3))))) → p4) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ p2) ∨ (p1 ∨ ((p5 ∧ ((False ∨ p1) ∨ p1)) → (((True → ((p1 ∧ p2) ∧ p1)) → (False ∨ p3)) ∨ (p3 → p3))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804094604606839181344297745541 : (((p3 → (((p4 ∧ (p4 ∨ False)) ∨ (((p4 ∨ ((((p3 ∧ p2) ∧ p5) → p4) → p2)) ∨ p1) → p4)) ∧ (((p1 ∨ p1) → p5) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641703953197706743005000215723 : (((((p1 ∨ p5) → (((p3 ∨ p2) ∧ ((p3 ∧ (p1 ∨ (((p5 → (True → (p4 ∧ p1))) ∧ (p3 → p3)) → False))) ∧ p3)) → p4)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77123466752133170020306644858 : ((((((p4 → p5) ∧ p1) → p3) → (((p3 ∧ (p5 ∨ ((p2 → False) ∧ (p5 ∨ p2)))) → (((p3 ∨ p4) ∨ p5) → p3)) ∨ False)) → False) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 → p5) ∧ p1) → p3) → (((p3 ∧ (p5 ∨ ((p2 → False) ∧ (p5 ∨ p2)))) → (((p3 ∨ p4) ∨ p5) → p3)) ∨ False)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h4.left
        let h9 := h4.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- One of the premise coincides with the conclusion.
            exact h8
          case inr h15 =>
            -- One of the premise coincides with the conclusion.
            exact h8
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h4.left
        let h18 := h4.right
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- One of the premise coincides with the conclusion.
            exact h17
          case inr h24 =>
            -- One of the premise coincides with the conclusion.
            exact h17
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h4.left
      let h27 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- One of the premise coincides with the conclusion.
        exact h26
      case inr h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- One of the premise coincides with the conclusion.
          exact h26
        case inr h33 =>
          -- One of the premise coincides with the conclusion.
          exact h26
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h34 := h1 h2
  -- False on the left can always be used.
  apply False.elim h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150449204921583855551805056836 : ((((((p2 → p2) ∨ (p4 ∨ (p1 ∧ (p1 → (p4 → p5))))) → (((p1 → p4) → p5) → p3)) → False) ∧ p1) → (((p5 ∨ True) ∧ True) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355153692745466283578189036543 : (p5 → ((((((p1 ∨ ((p3 ∧ p1) ∨ p4)) ∨ p5) ∧ (p5 → ((p1 → False) ∨ (False → p2)))) → p2) ∧ (p5 ∨ (p2 → (p4 → p2)))) → p2)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : (((p1 ∨ ((p3 ∧ p1) ∨ p4)) ∨ p5) ∧ (p5 → ((p1 → False) ∨ (False → p2)))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h6
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : (((p1 ∨ ((p3 ∧ p1) ∨ p4)) ∨ p5) ∧ (p5 → ((p1 → False) ∨ (False → p2)))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h13
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h11
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252676788373651975128631312556 : ((p5 → p4) ∨ (p4 ∨ ((((True → p4) ∧ False) ∧ ((((p2 ∧ p4) ∨ p1) → p2) → p4)) ∨ (True ∧ ((False ∨ (p5 ∨ (p5 → True))) ∨ p1))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317006756410379791019366775775 : (p3 ∨ (p3 → ((True ∧ p2) ∨ (((p1 ∧ False) → True) ∧ ((((p3 ∨ (p4 ∧ p4)) → p2) ∨ (((p5 ∨ p5) ∨ p4) ∨ True)) ∨ (p4 ∧ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55823019635648929859267623054 : ((((p2 → p2) → (p3 → False)) ∧ (p4 ∧ ((((False ∨ False) → ((p3 ∨ True) ∨ ((False ∨ (True ∧ (p3 ∨ p4))) ∧ p3))) → p1) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52357552281568510517726347932 : ((((False ∨ (((((p5 → p2) ∨ p1) → True) ∧ p1) ∨ p5)) ∧ (p4 ∧ p4)) ∧ ((((True → True) ∧ (p2 ∧ (True ∨ p3))) ∨ p1) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616884091850649899155523091812 : (((((((False ∨ (False ∧ p4)) → (False ∧ p2)) → (p5 ∨ p5)) → (p4 → ((p5 ∧ p5) ∨ (((p1 ∨ (True → p5)) ∧ p3) ∨ p2)))) ∨ p2) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∨ (False ∧ p4)) → (False ∧ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h3
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h14
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h15
    -- One of the premise coincides with the conclusion.
    exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319084891697586591993717164488 : (p4 ∨ (((((True ∨ (False ∨ (True ∧ True))) ∧ p3) → (((p2 ∨ (False ∨ p5)) ∧ p4) → True)) ∨ (False ∧ p3)) → ((p4 → p3) ∨ (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354876142433367167083991722138 : (p5 → ((p1 ∧ (((((((p5 → p5) ∧ (p2 ∨ (False → p2))) ∧ p4) ∨ (p5 → (p4 → False))) → p3) ∧ ((p3 ∨ True) → p4)) ∧ p1)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165275924714975407148355020551 : (((((((((p5 ∨ p4) ∧ p3) ∨ p3) → p3) ∨ True) ∧ p3) ∧ (p2 → p1)) → (p1 ∨ False)) ∨ ((((True ∨ p1) ∨ p1) → p2) → (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244434544655189040794533632188 : ((False ∧ p2) ∨ ((p5 ∧ ((p2 ∧ ((p3 → (p3 ∨ False)) ∧ ((False ∨ p3) ∨ ((p4 ∨ (p2 ∧ p2)) → (p2 ∨ False))))) ∨ (p3 ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



