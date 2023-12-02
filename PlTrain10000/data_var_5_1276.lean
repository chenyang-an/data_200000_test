variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51249753586304693022271356619 : ((((p3 ∧ p4) ∧ ((p3 → (p2 ∧ ((p4 ∨ p4) ∧ p5))) ∧ (p4 ∨ (True ∧ (True ∨ p4))))) ∨ (p2 → (p3 → (p3 ∧ (True → True))))) ∨ False) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219213140687634972026715621677 : ((False ∨ (p3 → (p3 ∧ p2))) → (((p3 ∨ (((True ∧ p1) ∧ (p3 ∧ p1)) ∧ p2)) ∨ ((True → p1) ∧ ((True ∧ p1) ∧ (p4 → p5)))) ∨ True)) := by
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
theorem thm_5_vars_164535084179591881535912071141 : ((((p3 ∨ (p3 ∧ (p3 → (p1 ∨ (p1 ∧ (True → p5)))))) ∨ ((p3 ∧ p1) ∨ False)) ∧ p5) ∨ ((p2 → False) ∨ ((False ∧ (False → True)) → p5))) := by
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
theorem thm_5_vars_44456114067963595132787935185 : (((((p2 ∨ True) ∧ (((True → p5) ∧ ((False ∧ p1) ∧ p1)) ∨ p3)) ∨ (p5 → ((p4 ∨ False) → ((p2 ∧ (p2 ∧ p3)) ∨ p1)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149320513987941634436759315550 : (((p4 ∧ True) → ((p2 → ((p3 ∨ p3) ∨ ((p4 ∧ (p3 → p3)) ∨ (True → p4)))) → (p2 ∧ (p4 ∨ p3)))) ∨ (((p2 → False) → p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750531718067119661652722212911 : (((True ∧ (((p3 → (p5 ∨ p1)) → ((True ∧ p4) ∧ (p3 ∨ ((((False ∧ False) ∨ False) → p5) → p2)))) ∧ (((p5 ∧ False) ∨ p4) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347818072050474472778779180329 : (p3 → (((False ∨ True) ∧ p4) → (((p5 ∧ ((p2 ∧ ((p3 → p1) → ((p3 → (p4 ∨ p1)) ∨ p2))) → False)) ∨ (p2 → (False ∨ p3))) ∨ p1))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110699287136377577733110250403 : ((((((p5 ∨ (p5 ∨ ((True ∨ (p2 ∧ p5)) ∨ (p1 ∧ p5)))) ∨ (False ∨ ((True ∧ p5) ∧ (p1 → p4)))) ∧ False) ∧ p4) ∧ p2) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670058026634014667964287850570 : ((((((False ∨ (((True ∨ p3) ∧ False) → p2)) ∨ p1) → ((p1 ∨ (p2 ∧ (p2 ∧ p1))) ∨ (p5 ∨ (p5 ∨ p3)))) ∨ (p4 ∧ (True ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302063992383612091048789595932 : (False ∨ (True ∧ (p5 → (((((p2 ∧ p4) ∧ ((((p2 ∧ p2) ∧ False) ∨ p5) ∧ (p4 ∨ p5))) → p1) → p4) ∨ (p5 ∨ ((p5 ∨ p4) ∧ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184576930425871306287638183895 : (((True ∧ (p4 ∧ ((p3 → True) ∨ (p5 → p1)))) → (p4 ∧ p5)) ∨ (True ∨ (((((p4 → p1) ∨ True) ∧ (p4 → False)) → p3) ∨ (False ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709041635899086452457279632750 : (((((p3 ∧ (True → p3)) ∧ ((False → p2) ∨ False)) → (p5 → ((p2 ∧ (True → (p5 ∧ ((p2 ∧ ((p1 ∧ False) ∧ True)) ∨ p2)))) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234895629606894232023686956982 : ((True ∧ True) ∧ ((((((((p1 → (p5 ∧ (p2 ∨ p4))) → p1) ∧ False) ∨ p4) ∨ ((p1 ∨ True) ∨ (p2 ∧ p2))) ∨ (p5 ∧ p3)) ∧ p2) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261105980665020371732335573479 : ((p4 → p3) → ((p4 ∨ p2) ∨ ((((p5 ∨ p5) ∨ (p1 ∧ p5)) ∧ (True → False)) → (p2 ∨ ((((p5 ∨ p4) ∨ p5) ∨ False) ∨ (p2 ∧ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h8 := h4 h7
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h11 := h4 h10
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h15 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h16 := h4 h15
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711475227139812709882556091781 : ((((p5 ∨ ((False ∨ (p4 ∨ False)) → p3)) ∧ (p2 → ((True → ((((p4 ∨ False) ∧ (p1 ∨ (p5 ∨ True))) ∧ False) ∧ (p5 ∧ True))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_463629835163787029730714699565 : ((((p2 ∨ (((p2 ∨ (False ∧ False)) → (((p4 → p3) ∨ (p4 ∧ p1)) → p2)) → p3)) ∨ (p5 → ((((p4 → p3) ∧ p2) ∨ False) → p2))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299438269920698444681747917320 : (False ∨ ((False ∨ (True → ((p1 ∧ False) ∨ ((True → False) → (((p2 ∧ ((True → ((p2 → p1) ∧ p3)) ∧ (False → p3))) → False) ∨ p3))))) ∨ p4)) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345402735516844134339474167939 : (p3 → (((((((p3 ∨ (p4 ∨ ((p1 ∧ p1) ∧ (True ∨ p2)))) → p1) ∨ ((p2 ∨ p3) ∨ p2)) → (False ∧ p4)) ∨ (p5 ∧ p2)) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165650949810305675911549854247 : ((((p4 ∧ ((False ∧ p3) ∧ True)) ∨ p5) ∨ (((p2 → (False ∧ (p1 → p3))) ∧ p2) → p3)) ∨ (p2 ∧ ((p4 ∧ (p2 ∨ (False ∧ p4))) ∨ p5))) := by
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
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256552492054422936939976634287 : ((False ∨ p5) → ((False ∨ True) → ((p2 ∨ (p3 ∨ (False ∨ (((p3 ∧ (p3 → (p5 ∧ False))) ∨ p5) ∨ (False ∨ ((p2 ∨ p3) ∧ False)))))) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229703042346740759702417010877 : ((p4 → (False ∧ p3)) ∨ ((False ∧ ((((((p3 ∧ p4) → p4) → (p5 ∧ (False ∧ (False ∨ False)))) ∨ p3) ∨ (p3 ∨ p3)) ∨ (p4 → p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117602827751364497795673124622 : ((p2 ∧ (p4 ∨ (p1 ∨ (p5 → ((p1 ∧ ((p1 ∧ (p2 ∨ ((True ∧ p2) ∧ (((False ∧ p4) → True) → True)))) → p3)) ∧ p4))))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58876615180546357410419697893 : (((False ∧ False) ∨ (p2 ∨ ((p4 ∧ (False → (False → (p2 ∨ p1)))) ∧ ((p1 → ((p1 ∨ p4) ∧ (((p1 ∨ True) → True) ∧ p5))) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46020751554407556601925394690 : (((((False ∨ (p2 → p1)) ∨ (p2 ∨ ((((p1 ∧ p1) → p1) → p1) → (((True → (p4 ∧ p4)) ∧ p2) ∨ p5)))) ∧ True) ∧ (p1 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51096246846649413997938741647 : ((((((((p3 ∨ p2) ∨ p5) ∨ (p3 ∨ p3)) ∨ p1) → ((p3 ∧ (True ∧ True)) ∨ p4)) ∧ p1) ∨ ((True ∨ True) ∨ ((p2 ∨ True) → p1))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302668496995420924166345887895 : (False ∨ (p2 ∨ (p1 → (p1 → ((p1 ∧ (False ∨ p4)) → ((((p1 → p3) ∧ ((((p4 ∧ p5) → p1) ∧ p1) ∧ (p5 ∨ False))) ∨ p2) ∨ p1)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45598690196390473708581542093 : (((p3 ∨ ((True ∧ (((p4 → p1) ∧ ((p5 → False) → p1)) ∨ (p3 ∧ p5))) → ((p1 ∧ (p1 → p5)) ∧ (True ∧ (p2 ∧ p4))))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43996258450020891826573924806 : (((((((p2 ∨ (True ∧ (p4 ∨ ((p2 ∧ p2) ∧ p3)))) → True) ∨ (p3 ∨ (p2 ∧ ((p2 ∨ False) ∨ True)))) → p5) → (p2 ∨ True)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66544632524084868367707617866 : ((True → ((p3 ∨ ((p4 → (p1 ∧ (p2 ∨ p4))) ∧ ((p3 ∧ False) → (((((p1 ∨ p1) ∨ p1) ∧ (p1 ∧ p2)) ∧ p1) ∨ p2)))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90922424459361914652525758565 : (((True → False) ∧ (p1 ∧ ((p2 ∨ ((p5 ∨ (((((False ∧ False) ∧ (p1 → p3)) ∧ True) ∧ p4) → (p4 ∧ (p5 ∧ p3)))) → p2)) ∨ p5))) → False) := by
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
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261218908475220454781412372192 : ((p4 → p5) → (((p2 ∧ (p2 → (p3 ∧ p4))) ∨ True) ∧ ((True → ((p1 → ((False ∨ p2) ∧ True)) → (False ∨ (p4 → (p5 ∨ False))))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44003423060684021415471378556 : ((((((p5 ∧ (True → p3)) ∧ ((((False ∧ (True ∧ (p1 ∧ p3))) ∨ p4) ∨ p2) ∨ (p2 ∨ True))) ∨ (p4 → p4)) → (p3 ∧ p3)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_93055366401656999218696939575 : ((True ∧ (((p1 → ((True ∨ p2) ∧ False)) → (p1 ∧ (p2 → True))) ∧ (((p4 → ((p3 ∨ p5) → False)) ∨ True) → (p5 ∧ (True ∧ p1))))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((p4 → ((p3 ∨ p5) → False)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111690838882908137132474282460 : (((((p1 → (((p1 → (p1 ∧ p4)) ∧ p3) ∨ ((((p4 ∨ p3) → (True ∧ True)) → p4) → (p3 ∨ p1)))) ∨ p4) → False) ∨ True) ∨ (True ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164746941327074804452680064056 : ((((p2 ∨ (((p1 ∨ True) ∨ p2) → (((p3 ∨ p5) ∨ p3) ∧ p1))) ∨ (p3 ∨ p1)) ∨ True) ∨ ((p3 ∨ (((p3 ∧ p4) → True) ∧ p3)) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595802046249983684799358137425 : (((((True ∧ (p5 ∧ (p1 → (p3 ∨ ((p3 ∧ False) ∨ p4))))) ∧ (((((p5 → (p1 → p2)) ∨ p4) → p4) ∧ (p2 ∨ p1)) ∨ p3)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115295080074311651015656854477 : ((((((p3 ∧ False) → (p3 → p2)) → (p5 ∨ p4)) ∨ True) → (((True ∧ (True ∧ True)) → (p1 ∨ False)) ∧ (True ∧ (p3 ∧ True)))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65315248850777966161625127755 : ((p3 ∨ (((p2 ∨ ((p5 ∧ True) → ((True ∨ p3) ∧ (True → (p5 ∨ ((p2 → (p2 → p4)) → p4)))))) → False) ∨ ((p5 ∧ p4) → True))) ∨ p4) := by
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
theorem thm_5_vars_51872541201656485138598788060 : (((((p5 ∨ p1) → ((p3 → ((p2 ∧ p1) → p3)) ∧ (True ∧ (p2 ∧ False)))) ∨ p3) ∨ ((((False ∨ p3) ∨ p3) ∨ (False → p3)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202708305274274814183477452872 : (((True → (True → p1)) → (p5 → p1)) ∧ (((p3 ∧ (p2 ∨ ((False ∧ (((p1 ∨ (False ∨ False)) → (False → p3)) → p5)) ∧ False))) ∨ False) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53610621709317781447270421749 : (((((p4 → ((p4 ∧ p5) ∧ p4)) → p4) ∨ (p5 ∨ p4)) ∧ ((p1 → ((False ∧ (((p1 ∧ p2) ∨ p2) ∨ (p2 → p5))) ∨ p2)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608337043974671551103116495936 : ((((((((False → p2) → p5) → (False ∨ (((p1 ∧ ((p5 → p2) ∨ p5)) ∧ (p3 → (p3 ∨ p4))) → (p2 ∨ p1)))) ∨ p2) ∨ False) ∨ p2) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313125022542308638089217381739 : (p3 ∨ ((((((False ∨ (((((True → (True ∨ p3)) → p4) ∧ p2) → False) ∨ p2)) ∨ p4) ∨ p2) ∨ p2) ∨ (p2 ∧ (False ∨ (p2 → p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264961989298683756937731460460 : (True ∧ ((p2 ∨ p4) → (((p3 ∧ True) → (p5 ∧ False)) → (p5 ∨ ((False ∧ p5) ∨ ((p3 → ((False ∧ True) ∧ p4)) ∨ (True ∧ (False ∧ p5)))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p3 ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
    -- True on the right can always be proven directly.
    apply True.intro
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (p3 ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : (p3 ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h12
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h13
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- False on the left can always be used.
    apply False.elim h15
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90083296504062833471352695446 : ((((False ∨ False) → p5) → (((p3 ∨ (p5 → p3)) → (((p1 → (p3 ∨ p3)) ∧ (p2 → (False → (p3 ∨ p2)))) → (True ∨ False))) ∧ p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ False) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599323526366306490910941004050 : (((((p1 ∧ p5) ∨ ((p1 ∧ ((((((True ∧ p5) → p1) ∧ p4) ∨ p5) → p5) ∨ ((p1 ∧ p4) ∨ (p2 → True)))) ∧ (p4 → p5))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350278219935990952680435079395 : (p4 → ((p5 ∧ ((False ∨ (((True ∨ (True → (p2 ∨ p3))) ∨ True) ∧ p2)) ∨ ((p5 ∧ p5) ∧ (p3 → (p4 ∧ ((p2 ∧ p2) ∨ p5)))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111343391620053375947462404237 : (((p3 ∧ (p1 ∧ ((p3 → p4) → (((p2 ∨ False) ∨ True) → ((p1 → ((True ∧ ((p3 ∧ True) → p4)) ∧ p1)) → p1))))) ∧ p3) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158909047208398600012861328812 : ((p1 ∨ (((False ∨ p3) ∧ (False ∧ (True → p3))) ∧ ((False ∧ (((True ∧ False) → p4) → False)) ∧ p4))) ∨ (True ∨ ((p4 ∧ (True → True)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185594560060484447647199061116 : ((p5 ∨ ((p4 ∨ p2) ∨ ((p4 ∨ (True → p1)) ∨ (p4 ∨ True)))) ∨ (p2 ∧ (((p5 → ((False → ((False ∨ p5) ∨ True)) ∨ p5)) → False) ∨ p3))) := by
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
theorem thm_5_vars_165508965062169511074344613365 : (((((p5 ∨ (p3 → ((p4 ∨ p3) → p4))) → p3) ∨ p4) → (p3 ∧ ((p2 → p1) ∧ p1))) ∨ ((((p2 ∧ True) ∨ True) ∧ p5) ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113790084674083970949672930647 : ((((True → False) ∧ (((((((p3 ∧ p3) ∧ p1) ∨ p2) → p3) → p1) ∨ (p2 → (False → (p3 → p2)))) ∧ True)) → (p3 ∧ p1)) ∨ (False ∨ p4)) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h13.left
  let h15 := h13.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h16 =>
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h18 := h12 h17
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h20 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h21 := h12 h20
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159501166675662827531386649684 : ((((p2 ∨ (p3 ∨ p1)) → (p4 → ((False → ((p5 → p4) ∧ ((p5 ∨ p2) ∨ True))) → True))) ∧ p4) → (((True → p2) → p1) ∨ (True ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733008496451751356241908159671 : ((((p2 ∧ p4) ∧ (((((p2 ∨ True) ∨ True) → p5) ∧ (p4 ∧ p2)) ∧ (p1 ∧ (((p5 ∨ True) → ((p1 ∨ False) ∧ True)) ∧ (p3 ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173222819606429609969506595868 : ((p5 ∨ (p2 → ((((True ∧ (p5 ∧ p2)) → ((p1 ∧ p3) ∨ False)) ∧ p5) ∧ p2))) ∨ (((False ∧ (False ∧ p1)) ∧ p5) → ((False → p3) ∧ False))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618730292908759795780382297057 : ((((((p1 ∧ True) → p4) ∧ ((False ∨ ((p1 ∧ (p5 ∧ False)) ∧ (((((p5 ∨ p1) ∨ p2) ∨ p1) ∧ p1) ∧ (p5 → True)))) ∧ True)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_463472888221044228643194560013 : ((((p2 ∧ ((((True ∧ ((p1 → False) ∨ ((p3 ∧ False) ∧ p5))) → True) ∨ p2) → p3)) ∨ (p1 → ((True ∨ p1) ∨ (True → (p2 → p2))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159935157504417809518224380762 : ((((p5 ∨ (False → ((False ∨ (p4 ∧ (((p2 ∨ p4) ∧ p1) ∨ (p2 ∨ p5)))) → p1))) → p5) → True) → ((p2 → ((p1 ∨ p4) ∨ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153592670184764366964327817940 : ((False → ((p3 → (p5 ∨ True)) ∨ (((p4 → (((p3 → p2) → p1) ∨ p4)) ∧ p1) ∨ (p2 → (False ∨ p1))))) → ((True → (True ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672363687241968767720136836038 : ((((((p3 → (False ∧ (True ∨ (((p1 ∧ False) ∨ (True → p4)) ∧ False)))) → (p5 ∨ (p5 ∧ (True → p5)))) → p3) → (p4 → (p4 ∨ False))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65904684481211188961393511620 : ((p4 ∨ (p1 ∧ (True → ((p1 ∨ (True ∧ (p5 ∨ (p4 ∧ (((p1 ∧ p3) ∨ True) ∧ p2))))) → (p5 → ((p2 ∨ p3) ∧ (p3 ∧ True))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342282727276035410908368311418 : (p2 → (((True ∨ (((False ∨ ((p2 ∨ False) ∧ ((p1 ∧ p2) ∨ p3))) ∨ p3) → p2)) → (True → p5)) ∨ ((p2 → (p2 → (p1 ∧ False))) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750906067294930749038438196343 : (((True ∧ ((((p4 ∧ (False ∧ True)) → p1) → (p3 ∨ p1)) ∨ (((True → (p4 ∨ False)) → ((p5 ∧ p2) → (p1 ∨ (p4 ∨ p5)))) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48163757545932837100622948366 : ((((True ∨ p1) ∧ ((((p5 ∧ (p1 ∨ p1)) ∧ ((p4 ∧ p2) ∧ p2)) ∨ p4) ∨ (((p1 ∧ p1) → (p3 ∧ True)) ∧ p4))) → (p5 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342688904723566846491491809573 : (p2 → ((((True ∨ (p2 → p3)) → (False ∨ False)) ∧ (p2 ∨ p3)) → (((((p2 ∨ p1) → p1) ∧ p5) → (True → p2)) ∧ (p4 → (p5 ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Implications on the right can always be decomposed.
  intro h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h12 := h2.left
  let h13 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h14 =>
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h15 : (True ∨ (p2 → p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h16 := h12 h15
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h20 : (True ∨ (p2 → p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h21 := h12 h20
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- False on the left can always be used.
      apply False.elim h23
  -- Conjunctions on the left can always be decomposed.
  let h24 := h2.left
  let h25 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h25
  case inl h26 =>
    -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
    have h27 : (True ∨ (p2 → p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h24, we can now drive its conclusion.
    let h28 := h24 h27
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h29 =>
      -- False on the left can always be used.
      apply False.elim h29
    case inr h30 =>
      -- False on the left can always be used.
      apply False.elim h30
  case inr h31 =>
    -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
    have h32 : (True ∨ (p2 → p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h24, we can now drive its conclusion.
    let h33 := h24 h32
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h34 =>
      -- False on the left can always be used.
      apply False.elim h34
    case inr h35 =>
      -- False on the left can always be used.
      apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136893841588180714725547783907 : (((p3 ∨ p5) ∨ (False ∨ (p4 → (((True ∧ ((p3 → (p5 ∧ (p3 → (True ∨ p2)))) ∨ (False ∧ p5))) ∧ False) ∨ p4)))) ∨ ((p1 → p1) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263689258866198331501608666855 : (True ∧ (((((p4 ∧ (((p1 → p4) → (p1 ∧ p2)) ∧ p4)) ∧ (p2 → True)) → p3) ∨ (True → p1)) ∨ (((p3 → (p3 → True)) ∧ p1) → True))) := by
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
theorem thm_5_vars_774068150281986140679717475759 : (((False ∨ (((True → (((p4 ∧ True) ∨ ((False ∨ p3) ∨ False)) → (p5 ∨ p2))) ∧ (False ∧ (p3 ∧ ((False ∧ p3) → p1)))) ∨ (p2 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167932928340924548167067616420 : ((((p2 ∧ p2) ∧ (p1 → ((p3 ∧ p4) ∧ p5))) ∨ (p1 → (((p3 ∨ p5) ∨ False) ∨ p5))) → ((((p2 ∧ (False ∧ p2)) ∧ p4) ∨ True) ∨ p1)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672072067367715153370379242276 : ((((((((False ∧ p1) ∧ (p4 ∨ (False ∨ p4))) → p4) ∨ (p1 ∧ (p1 ∧ ((p5 → p5) → (True ∨ p4))))) ∨ p5) → (False ∧ (p5 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148019788561570991022069768093 : ((((p2 ∨ ((((p1 → p3) ∨ p2) → p3) ∧ p5)) ∧ (False ∨ (False → ((False ∨ p5) ∧ True)))) ∨ (False ∧ True)) ∨ (p3 → (True → (p1 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86512911388914585551462874755 : (((p2 → (((p4 → (p3 → (p4 ∨ False))) → False) ∨ p2)) → (((True → True) ∨ (False ∧ (p1 ∨ ((p4 ∧ (p4 ∨ True)) → p5)))) ∧ False)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → (((p4 → (p3 → (p4 ∨ False))) → False) ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68447174158056945629302834133 : ((p3 → (False ∧ ((True ∨ (True ∨ ((((p5 ∨ False) ∨ p4) ∨ (p1 → (p1 ∧ p3))) ∧ True))) → ((p2 → ((False → p2) → p5)) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53093749623817681734707950772 : (((p2 ∨ (p3 ∨ ((p5 ∧ (p5 ∨ (p5 ∧ (p5 ∨ p5)))) ∨ p1))) ∧ (p4 → (True → (p3 → ((False ∨ (p2 → (p2 ∨ True))) ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234634530466627363282637002604 : ((p3 → (p2 → p3)) → ((True → (((p4 ∧ ((((p5 ∨ p2) ∨ (((False ∨ p1) ∨ p4) → p1)) → True) → (False ∧ p4))) ∨ p5) ∧ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218853674017192707155567348252 : ((p2 ∧ ((p5 → p3) → p5)) → ((p3 ∧ True) → (p1 ∨ ((p4 → ((p2 ∧ (p5 → p4)) ∨ ((False ∧ (False ∨ p5)) ∧ p5))) → (p4 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147011138889491877266434461354 : ((((p3 ∨ ((p4 → ((p3 ∧ p2) → False)) ∨ (((p2 → False) → (True → p5)) ∨ p1))) ∨ (p3 ∨ True)) ∧ p5) ∨ (False → ((True ∧ True) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141494903390674016379335995673 : (((p3 → (p5 → p2)) ∧ (p1 → (((p1 ∧ ((True → p5) → True)) → p5) ∧ (p3 → ((True → p1) → (p4 ∨ p3)))))) → (p2 ∨ (p1 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : (p1 ∧ ((True → p5) → True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h8
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337034892573035457042640197225 : (p1 → (((((((p1 → p1) → False) → ((p3 ∨ p4) ∨ (((p5 → p1) → p2) → (p3 ∧ (p4 ∧ p3))))) ∧ p2) ∨ p1) ∧ True) ∨ (p4 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622637687313526393996508009597 : ((((p4 ∧ (((True → ((p4 → p1) → ((((False ∧ p5) → True) ∧ p4) → True))) → (p2 → (p3 ∧ p2))) ∧ (True ∧ (False ∧ p4)))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_132692027891145046882525543496 : ((False ∨ ((p4 ∧ (False → p1)) → ((((p2 ∧ p3) ∧ (False → (p1 → True))) ∧ p5) ∨ ((p1 ∧ p2) ∨ (p1 → p1))))) ∧ (False → (p3 → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148753135489037452673228930477 : (((p3 ∧ ((p4 ∨ (p1 ∨ p5)) ∨ p5)) ∧ (p5 ∧ ((((((p3 → p3) ∨ p2) ∨ p3) ∨ True) → p2) → p5))) ∨ (p3 → ((False → False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50675231270944845871227346488 : ((((((p5 ∨ p1) → p2) ∨ p3) ∧ (((((p3 ∨ p1) → p1) ∧ p3) ∨ p3) ∧ ((False ∧ p2) ∨ p2))) → (((p3 ∨ p4) → p4) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50241028947809860465149963664 : ((((((((((p2 ∧ p1) ∧ True) ∧ p2) → (p2 ∧ p1)) → (p3 ∧ p1)) ∨ p2) ∨ (p2 → p5)) → p2) ∨ (((p4 ∧ p4) ∧ False) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40966204478872697304233611616 : ((((((p3 ∧ (p2 → (p2 ∨ p5))) ∨ p4) ∧ ((((p5 → (p3 ∨ (True → p5))) ∨ (p3 ∨ False)) → p4) → p2)) ∨ (False → p1)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166906705323467822104037342764 : ((((False ∨ ((True → (p5 ∧ p4)) ∨ p3)) ∧ ((p1 → True) ∧ (p3 ∧ (True ∨ p2)))) ∧ p5) → (False ∨ (p5 → (False ∨ (p4 → (False ∨ p3)))))) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h5.left
      let h10 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h5.left
      let h21 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h25
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h26
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h28
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h29
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150883720810901237342099731902 : (((((p5 ∧ (p3 → p4)) → p1) ∨ ((((True ∧ p3) → (True ∨ (p4 → (True ∨ p3)))) ∨ p1) ∧ True)) ∨ p1) → ((p2 ∧ p2) ∨ (p2 → p2))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
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
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344844288487426753513662748465 : (p2 → (p5 → ((((False ∨ p2) ∧ (p1 ∨ (((True → False) ∧ (p1 ∨ (p3 ∨ (p4 → p1)))) ∨ (p5 ∨ (p3 ∧ p4))))) ∧ p5) ∨ (p3 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46702169664931932346637853302 : (((p4 ∨ ((((False ∧ (p5 ∨ True)) ∨ (p5 ∧ p1)) ∧ ((((p4 ∧ p2) ∧ p4) → ((p3 ∨ p3) ∨ p5)) → True)) ∨ True)) ∧ (True ∨ p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319246104621801795713985882496 : (p4 ∨ (((p1 ∧ ((p2 → p4) → p2)) ∨ (p5 ∨ (p1 → ((p3 ∧ (p4 ∨ p2)) → True)))) ∧ (True → (True → (p4 ∨ ((False → p3) ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693843847895636901106505956472 : ((((((True → p3) ∧ ((p2 → p1) ∧ (p1 ∨ ((p2 ∨ p4) ∧ p4)))) → p4) ∨ (p1 ∨ ((p4 ∨ ((p4 ∨ p5) ∨ (False ∧ False))) → True))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49462446780212210575010277160 : ((((False → (((((p5 → (True → (p5 ∨ True))) → (False → p5)) → p1) ∨ (p2 ∧ (p4 → p2))) ∧ True)) ∨ True) → ((p4 ∧ True) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53291391855768291703061467633 : (((False ∨ ((p4 → ((p4 → p3) ∧ False)) ∨ (p4 → (p3 → p5)))) ∨ (((False ∨ (p2 ∨ p2)) ∨ p1) ∨ (p3 ∨ ((True → True) ∨ p2)))) ∨ False) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178765630172769172210269615660 : ((((p3 ∨ False) → False) ∧ (p5 ∧ ((p5 ∨ p5) → (p4 ∧ (p3 ∨ False))))) ∨ (False ∨ ((True ∧ ((p2 ∧ p3) ∧ ((p1 ∧ p5) → p5))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41797451398612173888509204094 : ((((p1 ∧ ((p4 ∨ p1) ∨ p3)) → (((((p1 ∧ ((False ∧ p2) ∨ (True ∨ p5))) → p3) ∨ (p1 ∧ p5)) → (p4 ∧ p2)) → p2)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789772102082075269306073173200 : (((p5 ∨ (((p4 → (True ∨ p5)) ∨ False) → ((p5 ∧ ((p5 ∧ True) ∨ p2)) ∨ (p4 ∧ (True → (((False ∧ p4) ∧ (True ∨ p1)) → p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803246850029549625411018876387 : (((p3 → (((p5 → ((((p5 → False) ∨ (p4 ∧ (p1 → ((p1 ∨ (p2 → p4)) → p3)))) ∨ (p3 ∧ p4)) ∨ p2)) ∧ (False ∧ p4)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49948425777175475576122750667 : (((((False ∨ (p4 → ((p2 ∧ True) ∨ (p2 ∧ True)))) → (True ∧ (p3 ∨ (p4 ∨ p3)))) ∨ (True ∨ True)) ∧ ((True ∧ True) ∨ (True → p1))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657464579800817639819810507246 : (((((p4 ∧ p4) ∨ (((p5 ∧ p4) → (True ∧ ((p3 → ((p3 → p1) → p5)) ∧ (p4 ∨ (p3 ∨ (p3 ∧ True)))))) → p1)) ∨ (p2 → p2)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51669117577721538640202899848 : ((((p2 ∧ (p3 → ((p5 ∨ p2) ∧ ((False ∨ (True → p2)) → (p1 ∨ p2))))) → p4) ∧ ((((p2 ∧ p2) ∧ p5) → (p2 ∨ p5)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



