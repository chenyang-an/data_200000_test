variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300558183107386274117622921751 : (False ∨ ((((True ∧ p4) → p3) ∧ ((((p2 → p5) → ((((False → p1) ∨ False) → False) ∨ p5)) → False) ∧ p4)) ∨ (False → ((p1 → p1) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172119408988544103350203055325 : ((((p2 → (p3 ∨ ((p1 ∧ (p5 ∨ p4)) ∨ p3))) ∨ p1) ∧ (p1 ∧ (p5 ∧ p2))) ∨ (True ∧ ((False ∧ (p2 ∧ p2)) → (True → (p3 ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181420404596284040686142433646 : ((p2 ∨ (p3 ∧ ((False ∧ ((p1 ∨ True) ∧ (p1 ∨ (p5 ∧ p4)))) → p1))) → ((False ∨ p5) → ((p2 ∨ p1) → ((False ∧ p5) ∨ (p1 ∨ p2))))) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660945850175085632152492438151 : (((((p2 → (True → ((p5 ∨ (False ∨ (p5 ∨ (p1 ∨ p5)))) → ((p4 ∧ p4) → ((p5 ∧ (True → False)) ∧ p3))))) → False) → (False ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119374742711883463837792266531 : ((p3 → (p5 ∨ (((p2 ∧ p1) → ((p3 ∨ p1) ∨ (p2 → (p4 → ((((p1 ∧ p1) ∧ p2) → (p1 ∨ False)) → False))))) → p5))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592703482621082703508022234619 : (((((((True ∧ ((((False ∨ (p5 → False)) → p5) ∨ (p4 ∨ p1)) → p1)) → (p4 ∧ (p5 ∧ p1))) ∧ p5) ∧ (p4 ∧ (p2 → p5))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181423966339119080751757236129 : ((p2 ∨ (p4 ∨ ((p3 ∨ p2) ∧ (((p4 ∧ p5) → (p4 → False)) → p5)))) → ((p2 ∨ (p4 → (p5 ∨ p2))) ∨ (((p3 ∧ False) ∨ True) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164597870201956480149707905856 : ((((p3 ∨ p1) → ((((p1 ∧ p5) ∨ p4) ∨ (p2 ∧ (p1 ∨ p5))) ∨ (p5 ∧ p5))) ∧ p4) ∨ ((p1 ∧ (p1 ∧ ((p3 ∨ p2) ∨ p4))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319046063536267841979416375925 : (p4 ∨ (((((p3 ∨ ((p4 ∨ p3) ∧ p5)) ∧ p3) ∨ True) ∨ ((False → (p5 ∨ (p3 ∧ (p2 ∨ p1)))) → p5)) ∨ ((False ∨ p3) ∨ (True ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314409853836797346644847021874 : (p3 ∨ (((((p2 ∨ (p4 → p1)) → (((True ∨ (p3 ∧ ((False ∧ True) ∨ p2))) ∨ p1) ∧ False)) → p3) → p1) ∨ (True ∧ ((p3 ∧ p3) → p3)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162373461688457737732189405663 : ((((True ∧ (p3 ∨ ((((p3 → p3) ∧ (p4 ∨ p5)) → p1) ∨ (p3 → p1)))) → p4) ∨ True) ∧ ((p5 ∧ (False ∨ p2)) ∨ ((False → True) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645663026738056774391402016909 : ((((p5 ∨ ((p4 → (((p4 ∨ (True → ((p1 → (p2 ∨ (p1 ∧ p3))) ∨ ((True → p5) ∨ True)))) → False) → p1)) ∨ (p3 ∧ p1))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242146453030906343769051488752 : ((p2 → True) ∧ (((p1 ∨ p3) ∨ (((p2 → ((p5 → p3) → p3)) ∧ p5) ∨ False)) ∨ (True ∨ ((p2 ∨ (p4 ∨ p5)) ∧ ((True ∧ p4) ∧ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691793605950414791516408205 : (((((p2 ∧ True) ∧ p3) ∧ ((False ∨ (False ∨ (p3 ∧ True))) ∨ p4)) ∧ ((((False → ((p2 → p2) → p2)) ∧ p1) ∧ p5) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341109851213467991280210873417 : (p2 → ((p5 → (((p4 ∨ True) → (((((p3 ∨ (False ∧ p1)) → (True ∧ p4)) ∧ False) ∧ ((True ∧ p5) → True)) ∧ p1)) ∨ (True → p5))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115278213894974008483337434873 : (((p5 ∨ ((((p1 → p1) ∧ p5) ∧ False) ∨ (p1 ∧ p2))) ∨ (((True ∧ (p2 ∧ ((p5 ∨ (True → False)) ∧ p3))) → p5) ∨ p2)) ∨ (p2 ∧ p2)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118481398736330053911416574150 : ((p3 ∨ ((p2 → (((False → False) ∨ (p1 → ((p3 → False) → (p1 → p3)))) → (False ∧ ((False → True) ∧ p5)))) ∨ (True → False))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750841501089755363903138066004 : (((True ∧ ((((p5 ∨ p5) → (p4 ∨ False)) ∧ (p1 → (p4 ∧ True))) ∨ ((p5 ∧ p5) → ((p2 ∧ False) → ((p4 ∧ (p3 → p2)) → p3))))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345686238237315491755456139041 : (p3 → ((p4 ∨ ((((((p1 ∨ ((p4 ∧ p2) ∧ p5)) ∨ p4) ∨ (((p2 ∧ p5) ∨ (p1 ∧ p1)) ∧ p1)) → p4) ∧ (p1 → p2)) ∧ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227734382552143704037511329549 : ((p1 ∧ (False ∨ p2)) ∨ ((p3 → ((p4 → (((p2 ∧ True) ∧ p3) ∨ (p2 ∨ (p2 → p2)))) ∧ p3)) ∨ ((((p2 → p4) ∨ p1) ∨ True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_112653415688172836676218711074 : (((((False ∨ (p5 ∧ p1)) ∨ (((p2 ∨ True) ∧ True) ∧ ((p1 ∨ (False ∨ False)) ∨ (p4 → False)))) ∧ ((p1 ∧ p2) ∧ p5)) → False) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809510631825643013338199142638 : (((p5 → (((((p2 ∧ True) ∧ ((True → (False → ((True ∧ p3) → True))) ∧ p2)) → p4) ∧ (p4 ∨ ((True → p3) ∨ (p5 ∧ p3)))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768869745526929091038351033431 : (((p5 ∧ ((p2 → (((p5 ∨ False) → p1) ∨ p2)) → (((p2 ∨ p5) ∨ (((p4 → ((p4 ∨ p3) → False)) ∨ p2) ∧ p3)) → (p5 ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299100079979412147404888368393 : (False ∨ (((((p4 → ((p1 ∨ (p2 ∨ (p3 ∨ p2))) ∧ (True → False))) ∨ p2) → (((p3 → ((p2 ∨ p1) → p4)) → p1) ∨ p4)) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62827813608179159544322267474 : ((p4 ∧ (((((p1 ∨ False) → (False ∧ p4)) ∧ p1) → p4) ∧ ((p3 ∨ ((((True ∨ p5) → p2) ∧ ((p1 → p4) → False)) ∨ True)) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204902179761887037573810474788 : ((((False → True) ∧ (p4 → p1)) → p4) ∨ (((p3 ∨ p4) ∧ ((((((False → p3) ∨ p3) ∧ (False → p2)) ∨ p3) ∧ p1) → p5)) → (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54179412480265238696038591166 : (((((p1 ∨ p3) → (p5 ∨ (p4 → p4))) ∧ p1) ∧ (((p1 → True) ∨ (p5 ∧ p5)) → ((p5 ∨ ((p2 ∧ p2) ∧ (p3 → p3))) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165753539434262524574132455312 : (((p5 ∧ (True ∧ (p2 → p2))) ∨ (((p3 ∧ p3) ∨ (p2 → (True → p5))) ∧ (p3 ∨ True))) ∨ (False ∨ (False → (True → (p4 ∨ (p4 ∨ p5)))))) := by
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
theorem thm_5_vars_186124203889356452096103155628 : ((((p1 ∨ (p1 ∧ (False ∨ True))) ∨ (p4 ∧ (p5 ∧ p1))) ∨ p4) → (p2 ∨ (False ∨ (((True → True) ∨ (p1 → (True ∧ p2))) ∨ (False ∨ p2))))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h5
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- False on the left can always be used.
          apply False.elim h9
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h11
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h17
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h19
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65990132585174842449520271524 : ((p4 ∨ (p3 → (((p2 ∧ (((((False ∧ p1) ∨ p4) ∨ (False ∧ p2)) ∨ (p2 ∧ (p1 ∨ True))) ∨ (p1 ∨ (p4 → p2)))) ∨ p3) ∨ p2))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116635702196224684715468938362 : (((p1 → p5) ∧ ((False ∧ (p4 → p5)) ∧ ((p4 → ((p3 ∧ ((p5 ∨ (p3 → p2)) ∨ (p4 ∨ p5))) → p1)) ∨ (p4 → p5)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190698346662614845264738051182 : (((((False ∨ (p1 ∨ p2)) ∨ True) ∨ p3) ∧ (p3 ∨ p4)) ∨ ((p5 ∧ (False ∧ p1)) → (True ∨ ((((False ∧ True) ∨ p1) ∨ (p5 ∨ True)) ∨ False)))) := by
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
theorem thm_5_vars_218038773032171899460275085462 : (((p2 ∨ True) ∧ (p5 ∧ p5)) → (False ∨ ((p4 → ((((p3 ∨ p2) ∧ True) ∧ (True → p5)) ∧ ((((p2 → True) → p1) → p5) ∨ p2))) ∨ p5))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330948322108126228945041516631 : (True → (p4 → (p2 ∨ ((True → p3) ∨ (True → (((False ∧ (p5 → False)) ∧ p1) ∨ (p2 ∨ (p1 ∨ (False → (((p2 ∨ p3) → True) ∧ p3)))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219247214523929562866091971860 : ((p1 ∨ ((True → p2) → p5)) → ((p2 ∧ (False ∨ (((p5 ∧ p3) ∧ ((p3 → (True ∧ p2)) ∨ p2)) ∨ p4))) ∨ (True ∧ (False → (True → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699976151832139948963724596195 : ((((((p1 → (False → p5)) ∨ False) ∨ ((p4 ∧ p2) → (p5 ∧ p5))) → (((p1 ∨ True) → (((True ∧ p3) ∧ p3) → p5)) ∧ (p1 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660177242417480034630987164414 : ((((((True → ((p1 ∨ p5) ∨ (p1 ∨ True))) ∧ (((((p2 → ((p1 ∨ True) ∨ p3)) → False) ∧ p2) → p5) ∧ True)) ∨ p1) → (False ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135343811833703085864889121293 : ((((p1 → p5) → (p4 ∧ (p1 ∧ ((p1 → p2) ∧ ((p5 → (False → p3)) ∧ (p1 → p5)))))) ∧ ((p4 ∧ True) → p2)) ∨ (p3 → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228545900775273079878392269284 : ((p1 ∨ (p4 ∧ p4)) ∨ ((p3 ∨ p3) ∨ ((((p3 ∨ False) ∧ ((p1 ∧ p1) → p1)) ∨ ((p1 → (p2 → (p4 ∧ True))) → True)) ∨ (p5 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234220995481465905387813874049 : ((False → (True ∨ True)) → (((p3 → False) ∨ ((p1 ∧ (p2 ∧ (p2 → p2))) ∧ (((p5 ∧ (p1 ∧ p3)) ∨ p1) ∧ False))) ∨ ((False → p3) ∨ p2))) := by
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
theorem thm_5_vars_255131595142601154672113970122 : ((p4 ∧ p3) → ((((((True → p2) ∨ ((p1 ∨ (p5 → (((p1 → False) ∨ p4) ∧ p2))) → (p2 ∨ False))) → False) → False) → p5) ∨ (False ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134122640544473826034681479861 : (((((True → ((p4 ∧ (p5 ∧ p1)) ∨ False)) ∨ (p1 ∨ ((p1 ∨ (p2 ∨ p2)) ∧ (False ∨ p3)))) ∨ (p2 ∧ p5)) ∨ True) ∨ (False ∧ (p2 → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224709722097034301603119005023 : ((p3 → (p1 → p3)) ∧ ((p2 ∨ ((p4 ∧ (False → True)) ∨ ((p3 ∨ p5) ∨ (((p3 ∨ ((False ∨ p2) ∨ p4)) ∨ (True ∨ p1)) ∨ p5)))) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640943855474208312976683830243 : (((((False ∧ p1) ∨ (((p1 → (p2 ∧ ((p1 → p2) ∧ False))) → ((True → p4) ∨ ((True → (p5 ∧ p2)) → p2))) → (p2 → p2))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53034282646010644378508017735 : (((((False → p5) → p4) ∨ ((p2 ∧ p1) ∧ (p4 ∧ (False → p3)))) ∧ ((p2 ∧ (p3 → p5)) ∧ ((True → (p1 ∨ (True ∨ p3))) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625649221857070057238996676881 : ((((p1 → ((((False ∧ p1) ∧ p3) ∧ (((((p5 ∧ p5) ∨ ((p1 → p5) ∧ False)) ∨ p5) ∧ True) ∨ (p3 ∨ False))) ∧ (p3 ∧ p5))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_103788260369840426474352777638 : ((((True ∧ ((((p4 → ((p2 → p1) → p4)) → (p2 → p5)) ∧ True) ∧ p5)) ∧ (p4 → (((False → p5) → p4) → p5))) → p5) ∧ (p2 ∨ True)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157751387475179615443814683766 : ((((p2 ∨ ((p4 → (False → p3)) ∧ True)) ∧ ((p1 ∨ p5) → p4)) ∧ (((p5 → p1) → p3) ∨ False)) ∨ ((True ∧ p1) → (p3 → (True ∧ p3)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38825676469192602759119235963 : ((((False ∨ (p4 → (p2 → p5))) → ((p1 ∨ (p2 → (p5 ∨ (p5 → (False → (p3 ∧ (p2 ∨ (p4 ∨ p3)))))))) ∧ (p4 ∧ p2))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118373892025935480787865304201 : ((p2 ∨ (((False → ((p5 ∨ True) ∨ p2)) ∧ ((p2 → (((True ∧ p4) ∨ True) ∧ p5)) ∧ p1)) ∨ ((p4 ∨ p1) ∨ (p1 ∨ p3)))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65476569956325653653487294916 : ((p3 ∨ (p1 ∧ (((p4 ∧ ((((p5 → p1) ∧ (p5 ∧ ((p3 → p5) ∨ p1))) → p4) → (p1 → True))) → p5) ∨ ((p1 → p1) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340755592284056689457537963668 : (p2 → ((((True ∨ p5) → ((((p2 ∨ (((p5 → (p4 ∨ p5)) ∨ p1) ∧ p5)) ∧ (p3 ∨ (p1 ∨ (False ∨ p2)))) → p4) ∧ p1)) ∨ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65165791194216797086548207998 : ((p3 ∨ ((((p3 ∨ (p2 → p3)) ∨ (((True ∧ ((p5 → (p2 → (True ∧ p5))) ∨ p1)) → p3) ∧ ((p3 → False) ∧ True))) → p5) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255192331243561278253399376115 : ((p4 ∧ p4) → ((((True ∧ ((True ∨ (((p3 ∧ (p2 ∨ p4)) ∧ ((p4 → True) ∧ (True ∧ p5))) ∨ p2)) ∧ p1)) → p4) → False) ∨ (True ∨ p3))) := by
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
theorem thm_5_vars_337756059861073687073601917999 : (p1 → (((p1 → (((p4 ∧ (False → ((False ∧ p3) ∧ (True → p4)))) → p5) ∨ p2)) ∧ p2) ∨ ((p4 → (p2 → False)) ∨ ((p4 ∧ True) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351170773415819452988684333943 : (p4 → ((((p5 ∧ p5) ∨ (((p5 ∨ p1) → (p5 ∧ False)) ∨ p4)) ∧ (False ∨ ((((p4 ∨ p1) ∨ False) ∨ False) ∨ p3))) ∧ (p1 → (p1 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709240394681930258283212535354 : (((((p4 ∧ True) ∨ ((p3 ∧ (p1 ∨ p5)) ∧ p4)) → ((p5 ∨ ((p5 → ((p1 → p1) ∨ (p2 → p2))) ∨ True)) ∧ (False ∧ (p1 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160093568509387477072718353288 : (((p4 ∨ ((p4 ∧ False) → (p1 ∧ ((p3 ∨ ((p3 ∧ p1) ∨ False)) ∨ ((p5 → p4) → False))))) → True) → (p3 → ((p3 → p5) → (p1 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244782301901493892818237213861 : ((p1 ∧ False) ∨ (p4 ∨ (p1 → (((False ∧ ((True ∧ (p3 → p5)) ∧ p4)) ∨ p3) ∨ ((((True ∨ p2) ∧ False) ∨ p1) ∧ (p5 → (p5 ∨ False))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76951016797806475478143309001 : ((((p4 ∨ ((((p4 ∧ p4) ∨ True) ∧ p1) ∧ False)) ∨ (((True ∧ True) ∧ (False ∧ p5)) → (p3 ∨ (((p2 ∨ p2) ∨ p5) → p4)))) → False) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∨ ((((p4 ∧ p4) ∨ True) ∧ p1) ∧ False)) ∨ (((True ∧ True) ∧ (False ∧ p5)) → (p3 ∨ (((p2 ∨ p2) ∨ p5) → p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h5.left
    let h9 := h5.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112138101215797499081759063334 : (((False ∧ (p2 ∨ ((False ∧ p3) ∧ (p3 ∨ ((((((p5 → ((p4 ∨ p4) ∨ p5)) → p3) → True) ∨ p1) ∧ p4) ∧ p1))))) ∨ p3) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618950082179857170003127607629 : ((((((False ∨ p4) ∧ p4) ∨ ((p3 → p4) ∧ (p3 → ((p4 → (((False → ((p3 → p3) ∧ True)) → p1) → p4)) ∨ (False → p3))))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39541338605111245544845742280 : (((False ∨ (p4 ∧ (p2 ∧ (((p4 → ((p2 ∧ p2) ∨ p2)) ∨ True) → ((False ∨ (True ∨ p1)) ∨ (True ∨ ((p4 ∧ p5) ∨ True))))))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644601827564576635296026828372 : ((((p1 ∨ ((((p2 ∧ p4) ∧ (p4 → (p5 → (p2 ∨ (True → p5))))) ∧ p3) → ((p2 ∨ p1) → (p1 ∨ ((True → p1) ∧ True))))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_239200705830577848723689256014 : ((p2 ∨ True) ∧ (p4 → (False ∨ ((True → (p4 → ((p2 ∨ (p3 ∨ True)) ∧ (((p4 → (((p3 ∧ p2) ∧ True) ∧ True)) ∧ p2) ∧ p4)))) → p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246032251899071056743530877722 : ((p4 ∧ False) ∨ (((p1 → (p2 ∧ p5)) ∧ (True → ((p3 → False) ∧ ((p3 → p3) ∧ p2)))) → ((False ∨ (p5 ∨ ((True ∨ p1) ∨ p1))) ∨ p1))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172826596603365607840397670151 : ((True ∧ (p1 ∧ ((p4 ∧ True) ∧ (False ∨ ((p3 ∧ (p5 ∨ (p2 ∧ True))) ∨ False))))) ∨ ((p3 ∧ p2) → ((p1 → p5) ∨ (p3 ∨ (p5 → p3))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135975839005917598750784492203 : (((((p3 → (True ∨ (p4 → (p1 ∨ p2)))) → p3) ∨ False) ∨ (((p2 → (p3 → p5)) ∧ (p5 ∨ p3)) → (True ∨ p1))) ∨ ((p4 ∧ False) ∨ p5)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_24807999795166287070052032421 : ((((p3 ∧ p4) ∨ p5) ∨ ((((p5 → (p2 ∧ (p3 ∨ True))) ∨ (True → ((p5 → (False ∧ (p2 ∧ p2))) → p5))) ∧ (p4 ∨ False)) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_119578545450538298678285320820 : ((p5 → ((p4 ∨ (p1 ∧ False)) ∨ (((((p3 ∧ False) ∧ (p3 ∨ (p5 → p2))) ∨ (p3 → False)) → False) ∨ ((False ∧ p4) ∧ p5)))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114621365217345455423429156975 : (((((p5 ∧ (False → (((p1 ∧ p3) → True) → (p1 ∧ p5)))) → (False ∨ False)) ∧ p1) ∨ ((p2 → ((True → p1) → False)) ∧ p1)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45352378788474528733789541351 : (((p4 ∧ (((((p4 ∨ p1) ∨ ((p2 ∨ (p5 ∧ p5)) ∨ (p2 → False))) ∧ p3) ∧ (((False ∨ p4) ∨ False) ∧ (p2 ∨ p5))) → p2)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172966947469884233098613977975 : ((p4 ∧ (((((p2 ∧ p1) ∧ p3) ∨ (p5 → p2)) ∨ p4) ∨ ((p3 → p5) → p4))) ∨ ((((p5 ∧ (True ∧ (False ∧ p1))) ∧ p2) ∧ True) → p2)) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624861463635325886279843341242 : ((((p5 ∨ ((p1 → ((((p5 ∧ (p4 ∨ True)) ∧ (p2 ∧ p4)) → ((p3 ∧ p1) ∨ p5)) → p4)) → (((p1 ∨ p3) → True) → p4))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337698909330263421255008044330 : (p1 → (((((p2 → p4) → p4) → ((p1 ∧ p4) → ((False ∧ False) ∧ False))) → ((True ∧ p3) ∨ p2)) → (((p5 ∧ p4) ∧ p4) ∨ (p1 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113202323272779791864287760139 : ((((((((((False ∨ False) ∨ (p1 ∧ p5)) ∨ (p4 ∨ (p2 → False))) ∧ p2) ∨ p4) → (p5 ∧ True)) → p5) ∨ p4) ∧ (p2 ∧ p2)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185297908571855809420935823068 : ((p2 ∧ (p3 ∧ (((False → p2) ∧ ((p4 ∧ p4) → True)) ∨ p4))) ∨ (True ∧ ((((((p5 → p1) ∨ False) → p2) ∧ (p4 → False)) ∧ True) ∨ True))) := by
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
theorem thm_5_vars_164933089626994148535764979735 : ((((True ∧ (p2 ∧ (p2 → ((p4 ∧ False) ∨ ((p2 ∨ p4) ∧ (p3 → p4)))))) ∨ p3) → False) ∨ (((True ∨ p2) ∨ False) ∨ (p1 ∧ (p4 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689408283291017894376189287934 : (((((p1 ∨ ((False ∧ p5) → (p2 ∧ (((True ∨ True) ∧ p2) ∧ False)))) → (p3 ∨ p2)) ∨ ((p5 ∨ (p4 → p4)) ∧ ((p3 ∨ p3) → True))) ∨ p1) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219283553131503374373756722567 : ((p1 ∨ (p5 → (p4 → p3))) → ((p4 ∧ ((p4 → (((False ∨ (p3 → False)) ∧ ((False → False) ∧ p4)) ∧ ((p2 → p4) → p5))) ∨ p5)) ∨ True)) := by
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
theorem thm_5_vars_197584530044994120893684905085 : (((p1 ∧ (p2 → (p2 ∨ p3))) ∨ (False ∨ p5)) ∨ (((((p5 ∨ p4) ∧ p1) ∧ p1) ∧ (((p4 ∨ (True ∨ False)) ∨ p1) → False)) → (p2 ∨ True))) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598588577652902310729830089697 : (((((p3 ∧ (p1 ∨ p1)) → ((p5 → ((p2 ∨ ((p1 → ((p2 ∨ p2) ∧ p3)) ∨ True)) ∨ (p2 ∧ p3))) ∨ (True → (p2 ∨ p4)))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601096433766793295785105042020 : ((((p1 ∧ (p3 ∧ (p4 ∨ ((p2 ∧ True) ∨ ((True ∧ p2) ∨ ((((p2 ∨ p5) ∧ p2) ∨ p4) → (p4 ∨ (False → (p3 ∧ p3))))))))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82265691961498184943333671707 : (((((((p2 → (((p1 ∨ ((p4 → False) ∧ p4)) ∨ p4) ∧ p2)) ∨ (False → p1)) ∨ False) ∧ True) → False) ∧ ((p5 → p1) ∨ (p5 ∨ p4))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((((p2 → (((p1 ∨ ((p4 → False) ∧ p4)) ∨ p4) ∧ p2)) ∨ (False → p1)) ∨ False) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : ((((p2 → (((p1 ∨ ((p4 → False) ∧ p4)) ∨ p4) ∧ p2)) ∨ (False → p1)) ∨ False) ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- False on the left can always be used.
        apply False.elim h12
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h11
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193708952967622879748632371067 : ((p2 ∧ ((p3 ∨ (((False → p4) → p3) → p3)) ∧ p2)) → ((p1 ∨ (((p1 ∧ (p3 ∧ ((True ∧ p2) → p2))) → p5) ∨ (p5 ∨ p4))) ∨ p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147447437003663740020651812840 : ((((p1 ∨ False) ∨ ((p3 ∨ ((False ∨ p1) → p3)) → ((((p2 ∧ p5) ∨ (p1 → p4)) → False) → False))) ∨ True) ∨ ((p1 ∧ (True → p4)) ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802935937237241073336567095151 : (((p3 → (((p5 ∨ (False ∨ (((p3 → p4) ∧ (((((p1 ∧ p4) → p1) → p1) ∧ p2) ∧ p5)) ∧ ((p3 ∨ p1) ∧ True)))) ∨ p3) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41512026396941831578166961677 : ((((((p5 → ((False ∧ p1) ∨ (p1 ∨ p5))) ∧ p5) ∨ p5) ∧ (((p4 ∨ (False ∧ ((p4 ∧ (p2 ∨ True)) ∧ p5))) ∧ True) → p4)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699816865204790540169889130099 : ((((((((p2 ∨ p3) → p3) ∨ True) ∧ (p5 ∧ p1)) → (p2 → p2)) → (((p3 → (p5 ∨ (True ∧ (p3 → p5)))) ∧ p4) ∨ (p2 → p2))) ∨ p4) ∧ True) := by
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
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736118128067169385542298995484 : ((((False → True) ∧ ((((p3 ∨ p5) ∨ False) ∨ ((p3 ∨ p2) → p1)) ∧ (((p1 ∨ (p3 ∧ (p4 ∧ p3))) ∨ (True → p2)) ∨ (p1 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199601202835956399345184586745 : (((((True → p3) ∨ (p5 ∨ p2)) → p3) → True) → (p3 ∨ ((p3 → (((((p2 ∧ p1) ∧ (p5 ∨ False)) ∨ (True ∧ p2)) ∧ p4) ∧ True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346585262907779364066991919302 : (p3 → ((((p5 ∨ ((p4 ∧ True) ∧ (p5 → (False → False)))) ∧ (p3 ∧ (p4 ∧ ((False → True) ∧ (p1 ∧ p4))))) ∧ False) ∨ (p3 ∨ (p5 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590973382298654112949476845238 : (((((p2 → (((((((p5 ∨ True) ∨ (((((p5 → p5) ∧ p1) ∨ True) ∨ p1) → True)) → True) ∨ True) → True) ∨ False) → p3)) → p2) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58959010777892810327774769381 : (((p2 ∧ p1) ∨ (((p1 → (p1 ∧ ((p4 ∧ p4) → False))) ∨ False) ∧ ((((True ∨ ((p2 ∨ (p1 ∨ p4)) ∧ p1)) → p2) ∧ True) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46889850633563656302091022717 : (((((p3 ∧ ((p2 ∨ True) ∧ (((((p2 → False) ∧ True) ∨ (p3 ∨ p3)) ∧ True) ∨ (False ∨ (True → False))))) ∨ p4) ∨ True) ∨ (p2 ∧ p3)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150526717798899205462689607530 : ((((True ∧ (p5 ∨ ((((p4 → p2) ∨ p1) → p5) ∧ p5))) ∨ (((False ∨ (p4 → False)) ∨ p5) ∨ p4)) ∧ p2) → ((p1 ∨ True) ∨ (p4 → p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_878957311080973894281738526419 : ((((p5 ∧ (((False → p5) → ((((((p5 ∨ True) ∧ (p4 → p1)) ∨ p4) ∧ p3) ∧ p1) ∧ (p2 → p5))) ∧ (p4 ∧ p5))) ∧ (p3 ∨ p1)) → p3) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h12 : (False → p5) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h13
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h14 := h6 h12
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- One of the premise coincides with the conclusion.
    exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200351589742638274848455595819 : (((True → True) ∧ ((p3 ∨ (p5 → p3)) ∨ p4)) → (p3 → ((True → (p2 ∧ p1)) → ((False ∨ p5) ∨ (p2 → (((True ∧ p5) → p5) ∨ p1)))))) := by
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
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h19
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- One of the premise coincides with the conclusion.
    exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_430622754358258713910425966780 : (((((p5 ∧ (p1 ∧ p3)) ∨ (p5 ∧ ((((p4 → True) ∧ (((p1 ∧ (p3 ∧ True)) → False) → (False ∨ p4))) ∧ False) ∧ False))) ∨ (False → p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47007509204211718757057632302 : (((((False ∧ p3) → (((((p2 ∨ (True ∨ (True → False))) ∧ p4) → (False ∨ p4)) ∧ (p5 → (False ∧ p1))) ∨ p3)) → p1) ∨ (True → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



