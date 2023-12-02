variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179533195881872948160814465221 : ((p1 → ((((p3 ∨ p5) ∧ (p2 → (p1 ∧ True))) ∨ (p2 ∨ p4)) → p5)) ∨ ((p3 → p2) ∨ (((p3 ∨ True) → ((p2 ∨ p4) ∨ p1)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187650916287236015771607543679 : ((p5 ∨ (False → ((p2 ∧ False) → ((p1 → (p5 ∨ p2)) ∧ p3)))) → (False ∨ ((p4 ∨ (True ∧ True)) ∧ (True ∧ ((p3 → p2) ∨ (p4 → p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234767430478446712075070455747 : ((p4 → (p5 → False)) → ((p3 ∧ (p4 ∨ True)) ∨ ((p4 ∨ ((False → (p2 → ((True ∧ p2) → (p2 ∨ ((p4 → p3) → p1))))) ∧ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50169256642530221153146633792 : ((((((p2 ∨ ((False ∨ ((p3 ∨ p1) ∧ (p3 → False))) ∨ (False → (p4 ∧ p2)))) ∨ p5) ∧ p5) ∧ p2) ∨ ((p3 → p2) → (False → False))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591398510081815956673107933923 : (((((((p4 ∧ p5) ∧ p4) ∨ (((p5 → (p1 ∧ p3)) ∧ (True ∨ p3)) ∨ (((False ∨ p5) ∧ False) ∧ (True ∨ p5)))) ∧ (p1 ∨ p4)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246556990614426041928915811337 : ((p5 ∧ p2) ∨ (((True ∧ (((True → p2) → (p3 ∨ p2)) → (p3 → ((False ∧ ((p3 → (p3 ∧ p5)) ∧ (p4 ∧ p1))) ∨ p5)))) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58419056851230079057701594387 : (((p2 ∨ p3) ∧ (((((p2 ∨ p1) ∨ p3) → ((p5 ∨ p1) ∧ p4)) ∨ p1) ∧ (((p4 ∧ p1) ∧ (True ∧ p2)) ∧ (False ∨ (p4 → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184878339443699225209453547369 : (((p3 ∧ (False ∨ True)) ∧ (p2 ∨ (((False ∨ True) ∨ p1) → p3))) ∨ (False ∨ (((p4 ∧ (p3 → ((p2 → p3) ∧ (p2 ∧ p1)))) ∧ True) → p4))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184279018736582798645253113904 : (((((p5 ∨ (True → p4)) → False) ∧ (True ∧ (p2 → p2))) → p5) ∨ (((p4 ∨ ((p1 ∧ (False ∨ p2)) ∧ (p5 → p3))) ∧ (p1 → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168950024705283272103027723823 : ((True → (p1 ∨ (((p2 → (p2 ∧ True)) ∧ (False → p4)) ∨ (((p3 ∨ p2) ∨ False) ∨ p3)))) → (p2 → (p4 ∨ ((p1 ∨ p4) ∨ (False → p5))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55321229470702577118820112596 : (((p2 ∨ (((p3 ∨ p4) → p4) → p4)) ∨ ((p3 → (p4 ∧ ((p3 ∨ (((True ∧ False) ∨ p2) → p4)) → False))) ∨ ((p1 ∨ p2) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159053775560499206398039732315 : ((p5 ∨ (((((p1 ∨ p5) → (((True → p5) ∨ p2) ∨ False)) ∧ p4) → p1) ∧ (p4 ∨ (True ∨ p3)))) ∨ (p3 → ((False ∧ p4) → (False → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785616391646882934305247402413 : (((p4 ∨ ((((p2 → ((((False ∧ (p5 ∨ (p3 ∧ p2))) → p4) ∨ (p2 ∧ True)) ∨ ((p4 ∨ (True ∧ p3)) ∧ p4))) → p2) ∨ p1) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719790885024153595899842118516 : ((((p2 → ((p1 ∨ p3) ∨ False)) ∨ (((((p5 ∨ p1) ∧ (((True ∧ (p4 → p4)) ∨ (p3 ∨ p2)) ∨ p1)) → p4) ∧ p3) ∨ (False → True))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_356007251830256954058147490165 : (p5 → ((p5 → (p5 → ((p3 → (((p2 → False) ∨ p2) ∨ ((p2 ∧ (p1 ∧ p2)) ∨ p5))) ∧ (p3 → True)))) ∧ (((p3 ∨ False) → p2) ∨ p5))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593969589901046496850846367836 : ((((((p5 ∧ p5) ∨ ((((p4 ∧ False) ∧ ((p1 → True) ∨ (p1 → p4))) → False) ∧ (p5 ∧ p5))) ∨ ((p2 → False) ∧ (p2 → p1))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190433084835102612563829970635 : (((p5 ∨ ((True ∨ False) ∧ (True ∧ (False ∧ p3)))) ∨ p3) ∨ ((False ∧ p5) ∨ ((((False ∧ p4) ∧ (p2 → (p3 ∧ p3))) → (p3 → p4)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53603202589015587515915570089 : (((((p4 → ((p1 ∨ p1) → p1)) → p1) ∧ (p4 ∧ p5)) ∧ (((True ∧ (False → p4)) ∨ ((p2 → p5) → p3)) → ((p2 ∧ p2) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185592778681888534311893617758 : ((p5 ∨ ((p1 → (True ∧ p3)) → ((p3 ∧ p5) ∧ (p5 → p3)))) ∨ ((p5 → ((((((p4 ∨ False) → p1) ∧ p3) ∧ p1) ∧ p5) ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113130593705156603556600008855 : (((p1 → (True → (((p1 ∨ ((p1 ∧ (True → False)) → p3)) ∧ p5) → (((True → (p4 ∧ False)) → p4) ∨ (True → True))))) → p4) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89102033680695866371742399650 : ((((True → False) ∨ False) ∧ ((p4 ∨ (p4 → (p2 → ((p5 ∧ p4) ∨ ((((p4 → (p3 ∨ p2)) → (p2 ∧ p4)) ∧ p5) ∧ p4))))) ∨ False)) → p3) := by
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
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628066326500102443684622105039 : ((((((p2 ∧ (p1 ∧ (False → p2))) ∨ (((((False → (((p3 ∨ p5) ∧ p2) ∧ False)) → False) → True) ∧ (True ∨ True)) ∨ p5)) ∧ p3) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114021091512767696655647768237 : (((((p1 ∧ False) ∧ (p3 ∧ (p1 → (False ∧ ((p1 → (p2 ∨ ((p2 → p3) ∧ p5))) ∧ p4))))) ∨ p3) ∨ ((p5 → p5) → True)) ∨ (p1 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662728870128417328200510636258 : (((((p3 → (p1 ∨ (p3 ∨ p4))) ∨ (True ∨ ((False ∧ (((p5 ∨ p4) ∨ p2) → False)) ∧ (((p3 ∨ p5) ∨ p2) ∧ p1)))) → (p4 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213572354386395189886596218753 : ((((p3 ∨ p1) ∧ p3) ∨ p4) ∨ ((p5 → (p2 ∨ p1)) → (((p2 ∨ ((p4 → p4) → (False → (p3 → p1)))) ∨ p1) ∨ (p2 ∨ (p3 ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197393192609688461182536889772 : (((p4 ∨ (False ∨ (False ∨ (p5 ∧ p1)))) → p2) ∨ (((p4 ∧ (((p1 ∨ p1) ∨ p2) ∨ ((p4 ∨ p5) ∧ (p3 ∨ (p1 → p1))))) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342479328187298548879526605731 : (p2 → (((p3 ∧ (((p1 ∧ (False ∨ p2)) → (p3 ∧ (p4 ∨ p1))) ∨ p2)) → p4) ∨ (p2 ∨ (((p1 ∨ (p1 ∧ (False ∧ p1))) ∧ p5) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198196765309660317620940840093 : (((p1 → p5) → (p5 ∧ ((True ∧ p2) → True))) ∨ ((p1 → True) ∧ ((((p3 ∧ (False ∧ p1)) ∨ (p5 ∨ p2)) ∨ True) ∨ ((p2 ∧ False) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98911139933930852148815938663 : ((True → (((((p2 → (((False → ((True ∧ (p2 ∧ p2)) ∨ p1)) → p2) ∧ (p3 ∧ (p3 ∧ p3)))) → False) → False) ∧ p1) ∧ (p2 ∧ p2))) → p2) := by
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
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135200169100190067568277233091 : (((((p5 ∨ True) → ((p5 → (p1 ∧ (p5 ∧ p2))) → ((p3 ∧ True) ∧ (p1 ∧ p1)))) ∧ (p4 → False)) → (p5 ∧ p5)) ∨ (p4 ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38036250201136849791200624371 : (((((((p4 → (False → ((False → True) ∨ ((p1 ∧ p2) → p2)))) → (True → (p4 ∧ p2))) ∧ (p4 ∨ False)) ∨ p2) → (p2 ∧ p2)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259066813288629929781045750882 : ((True → p5) → (((p4 ∧ ((p2 ∨ (((p3 ∨ p3) ∧ (p3 ∨ (p4 → ((False ∧ (p5 ∨ (p5 ∧ False))) ∨ p4)))) ∧ p4)) ∨ p2)) ∨ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47616057053547943304226383587 : (((p5 → (((False ∨ p2) ∨ (True → ((p3 ∧ (((p5 ∧ False) ∨ p4) ∧ True)) ∧ ((False ∨ False) ∧ (p3 ∧ False))))) ∧ False)) ∨ (True ∨ p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248044875586434780261417024805 : ((p1 ∨ p5) ∨ (((p1 ∨ p4) ∧ False) ∨ ((p4 ∧ (p4 ∨ (p3 ∧ (True ∧ (p1 ∨ p2))))) ∨ (False → ((p1 ∧ p5) ∧ (p2 ∨ (True ∧ p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78250068949137947406384284705 : (((p3 → (p2 ∨ ((((((((p2 ∧ p1) ∨ (p1 ∧ True)) ∧ p3) ∧ p4) ∧ ((p1 → (True → False)) → p4)) ∧ False) ∧ p1) ∨ True))) → False) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → (p2 ∨ ((((((((p2 ∧ p1) ∨ (p1 ∧ True)) ∧ p3) ∧ p4) ∧ ((p1 → (True → False)) → p4)) ∧ False) ∧ p1) ∨ True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214175062006861294080327458096 : ((((True ∨ p2) → True) → p3) ∨ ((p2 ∧ ((((((True ∧ ((p1 ∨ ((False ∨ p4) ∨ p3)) ∨ p3)) ∧ p3) ∨ p1) ∧ p2) → False) ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65742342904067962170128593984 : ((p4 ∨ ((((p5 → p5) → p1) ∧ ((False ∨ ((p3 ∨ p3) ∧ (p3 ∨ (True ∨ (p3 ∨ (p4 ∨ p5)))))) ∧ p1)) ∨ (p1 → (p5 ∨ True)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_652463247891885350332123623814 : ((((p5 ∧ (p2 ∧ ((((p3 → (p2 ∨ p4)) → p1) ∨ ((((True → ((p2 → p5) ∨ p3)) ∧ p5) ∧ p1) ∨ p4)) ∧ p2))) ∧ (False ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259042653013049911532228169090 : ((True → p4) → ((p3 ∨ False) → (p2 ∨ (((((p2 ∧ (p2 ∨ (p4 → p1))) ∨ (p5 → p5)) ∧ (p5 → ((p5 → True) → True))) ∧ True) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
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
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666334089939694469155949324567 : ((((((((True ∨ True) ∧ True) ∧ (p4 ∨ (False → True))) ∧ (p5 ∨ (p3 → (p5 ∧ p1)))) ∧ ((p4 → p5) ∧ p4)) ∧ (p5 ∨ (p4 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307131554295996123646293321212 : (p1 ∨ (False ∨ ((((p1 → ((p5 → p4) ∨ (((True → p2) ∧ (p1 ∧ p5)) → ((p4 → False) ∨ True)))) ∨ p2) ∨ (p2 ∨ p3)) ∨ (p3 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118180055784981937564796733269 : ((False ∨ (p3 ∧ (((p4 ∧ (True ∧ (True ∧ p2))) ∧ (((p5 → p5) ∨ p1) ∨ p4)) → (p5 ∨ (p3 ∧ ((p4 ∨ p3) ∧ False)))))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585519498090900125088758187262 : (((((((p2 ∧ ((((True ∨ p1) ∧ (p5 ∨ (p4 → True))) ∨ p3) → ((False ∨ True) ∧ (p4 → True)))) ∧ (True ∨ p5)) ∨ p5) ∧ True) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_239160472812481724323867724033 : ((p2 ∨ True) ∧ (((p4 ∨ p5) → ((p3 ∨ ((True → p4) ∧ p2)) ∧ (True ∨ ((p5 ∧ p2) ∨ (p3 → (False ∨ (p3 ∨ p4))))))) ∨ (p2 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206836056042574966878700967173 : ((p5 → (p5 ∧ (p2 ∨ (p4 ∧ p4)))) ∨ (False ∨ (False ∨ (False → ((((p4 → ((True → (p2 ∨ True)) ∨ (True ∨ p2))) → p5) ∧ False) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216049495678306331316397057837 : ((p5 ∨ (p2 ∧ (p3 → p1))) ∨ (False ∨ (((p4 ∨ (p3 ∨ ((p4 ∧ False) ∧ p2))) ∧ p2) → (False ∨ (p2 ∨ (((True ∧ p1) ∨ p3) → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338051643215672399241879628288 : (p1 → ((p3 ∨ (p4 ∨ (((True → p2) ∧ p3) → (p5 ∧ True)))) ∨ ((p3 ∨ (((p2 ∨ (p2 → (p1 → p2))) → p3) ∨ p1)) ∨ (p1 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322415001459172107970482325378 : (p5 ∨ (((((p3 ∧ ((True → p4) → (p4 ∧ p1))) → p3) ∧ p5) → (p3 ∨ (((p3 ∨ p5) → ((p3 → False) ∨ p3)) ∨ (False → False)))) ∨ p1)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115837117486910522227528207183 : (((p1 ∧ (p1 ∨ (True → False))) ∧ ((p5 ∨ ((p3 ∧ (p5 ∧ p1)) ∧ (p5 ∧ False))) ∨ (True ∨ (p1 ∨ ((p2 → p4) → p2))))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304771144102061727064690395267 : (p1 ∨ ((False ∨ ((p1 ∨ p2) ∨ (False ∨ (((p3 ∧ ((((p3 ∧ ((p3 ∧ p4) ∨ False)) → True) ∧ p5) → p2)) ∧ p2) → p3)))) ∨ (p4 ∧ True))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192235400580129000361168543112 : ((((((p4 ∨ p1) ∨ p4) → False) ∨ (True ∨ p3)) ∧ p1) → ((((True → (p2 ∧ p5)) ∨ (((True ∧ (p1 ∧ p2)) → p4) → p4)) → p4) ∨ p1)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619908271328693979306508121393 : (((((True → p1) ∧ (((p3 ∧ (p5 ∧ ((p4 ∨ True) ∧ (p3 ∧ p2)))) → (True ∧ p5)) → (True → (p2 → ((p2 ∧ p3) ∨ p3))))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774736584139884755033993748729 : (((False ∨ ((((p2 → p1) ∨ p4) → ((p2 → True) → p5)) → ((p2 ∨ False) ∧ (((p4 → (((p1 ∧ p1) ∧ p5) → p5)) ∧ p5) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147172967993649254617471469499 : (((False ∨ ((p5 → p3) ∧ ((p2 ∨ p5) ∧ ((p1 → (p1 ∧ (p4 ∧ p4))) ∨ (p1 ∨ (p4 ∧ p5)))))) ∧ p5) ∨ (p1 ∨ (p4 ∨ (False → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149879131443129445219551634568 : ((p2 ∨ ((p3 ∧ ((False ∨ False) ∨ (p2 ∨ (p2 → ((p5 ∧ True) ∧ p5))))) ∨ (((p1 ∨ p4) → p3) → p3))) ∨ (((False → False) ∨ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217236370803115422557379400344 : (((True ∧ (p4 ∧ True)) ∨ p3) → (p5 ∨ (((p2 → True) ∧ True) ∧ ((p2 ∨ (True → (((p1 → True) → p2) → (p1 ∨ (p2 ∧ p1))))) ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135044019979934620220744133867 : (((((p1 ∧ ((p4 → ((p3 ∧ p4) ∧ (p4 ∨ p2))) ∨ ((p3 ∨ p4) → (True ∧ False)))) ∨ False) ∨ p3) ∨ (p3 → False)) ∨ ((p2 → True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164858691167478770001003215696 : (((p1 ∨ (((p5 ∧ False) → p1) → (((p1 ∨ (p1 ∧ (p1 ∨ p1))) → True) ∧ p1))) ∨ p2) ∨ (p5 ∨ (((False → (p1 → False)) ∧ p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347851262118797755185339152877 : (p3 → ((p1 ∧ (p1 → p1)) → (True → ((((p2 ∧ p1) ∨ (((p4 → (p3 ∧ p3)) ∨ p1) → (p5 → p5))) → ((True → p4) ∨ p3)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49537986245387374355948594295 : (((((p5 ∨ (((((p4 ∧ p3) ∨ (p2 ∨ False)) ∨ p3) → p4) → ((False → p1) → False))) → p2) → (p5 → p4)) → ((p3 → p1) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62722677055819879539350990192 : ((p4 ∧ ((p4 → ((((((p5 → True) ∨ (p5 → p5)) ∧ (p5 ∨ (p1 ∨ (p4 ∨ p1)))) ∨ (p2 ∨ p1)) ∧ (p5 ∨ True)) → p5)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301139319938251533647993597453 : (False ∨ ((((p2 ∧ p3) ∧ ((True → p2) ∧ True)) ∨ p5) ∨ (p3 → (False → ((((p1 ∧ p3) ∧ (p5 ∨ p4)) ∨ ((p4 → p1) ∨ False)) ∧ p2))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160612282157293716778406992901 : (((p3 → ((p5 ∨ ((p2 ∧ (p4 ∨ True)) → p4)) → p3)) ∧ ((p4 → p1) ∨ ((False ∨ False) → p1))) → ((((p5 ∧ True) → p4) ∧ p4) ∨ True)) := by
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
theorem thm_5_vars_324174488652910030801770215519 : (p5 ∨ (((p3 ∨ False) ∧ ((((p4 ∨ p1) ∧ p1) ∨ p2) ∧ p5)) ∨ (p3 → (p4 ∨ (True ∨ (p1 ∧ ((False → False) ∧ ((p4 ∧ p5) ∨ p1)))))))) := by
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
theorem thm_5_vars_231691584587358685162237722112 : (((p1 ∧ p4) → False) → ((p4 ∧ (p2 ∧ p1)) ∨ (p4 ∨ (((True ∧ ((p5 ∨ True) ∧ (False → p1))) ∨ ((p5 ∨ (True → False)) ∨ p5)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218316053385233488396156785980 : (((True → False) ∨ (p1 ∨ False)) → (p4 → (p1 ∨ (True ∧ (((p3 ∨ (p1 → (((p5 ∨ (p3 ∨ p5)) ∧ p4) ∧ (False → False)))) ∧ p5) ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64969739793050879359679110439 : ((p2 ∨ (((p4 ∨ ((p4 → p1) ∨ p1)) ∧ p2) → ((((p5 ∨ ((p3 ∧ True) ∨ p3)) ∨ p2) ∨ False) ∧ ((p2 → (p3 ∧ p4)) → True)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  -- Implications on the right can always be decomposed.
  intro h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347451938498429106269214751368 : (p3 → (((p3 ∧ p5) → (True ∨ (p4 → p3))) ∧ ((p2 ∨ (p1 ∨ True)) ∧ ((p2 ∧ True) ∨ (p5 ∨ ((p1 ∧ p3) → ((p4 ∨ p5) ∨ p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138142530805536247139229610882 : ((p1 → (((p1 ∨ ((False → p2) ∨ True)) → ((p2 ∧ p5) → ((p3 → (p2 ∨ ((p5 → p1) ∧ p1))) → False))) ∧ p2)) ∨ (False → (p2 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259868408133547885754140813890 : ((p1 → p4) → ((((False → (p1 ∨ ((True → p1) ∨ False))) ∧ ((((p4 ∨ p2) ∨ ((p1 ∧ p1) ∨ p3)) ∧ False) ∧ False)) ∨ True) ∨ (p2 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133832476383070641775054372796 : ((((p3 ∧ p5) → ((((((True ∧ False) ∧ (p2 ∧ True)) ∨ True) → False) ∧ ((False ∨ (p3 ∨ p4)) ∨ p1)) ∨ p2)) ∧ False) ∨ ((False ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49306173605383304817792476791 : (((p1 ∨ (((False → (p1 ∧ (p3 ∧ (p1 ∨ (True ∨ ((p3 ∧ p1) ∧ (p1 ∧ p1))))))) ∨ p3) → (True → p4))) ∨ (p1 → (p2 → p2))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245768592965327126980304054861 : ((p3 ∧ p3) ∨ (((((((p3 → ((p1 ∧ p4) ∧ True)) ∨ p1) ∧ (p5 → p1)) ∧ p1) → p5) ∨ (((p1 ∧ (p5 → p4)) ∧ True) → p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345336009427329410127004059102 : (p3 → ((((p5 ∧ (p1 ∧ p5)) ∨ (p5 ∧ (((((p4 ∧ p3) ∨ ((p5 ∨ p1) ∨ p3)) ∨ p5) → True) ∧ (True ∨ (p5 → p3))))) ∧ False) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110867284264124127493441070211 : (((((((p2 ∨ False) ∧ (((p5 ∨ (p3 ∧ (p3 ∨ (p1 → p5)))) ∨ p5) ∧ (p4 ∧ p2))) → (True ∧ p5)) → p3) → False) ∧ p2) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303756680447105294701823471879 : (p1 ∨ (((((((p2 ∨ p1) → True) ∨ (p1 ∨ ((((((p2 ∧ p2) ∧ p1) ∧ True) → p1) → p5) ∧ False))) ∧ p4) → (p5 → p3)) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179095165054249599998989952670 : ((False ∧ (((p3 ∨ p2) ∨ ((((True ∨ p2) → p3) → p3) ∧ p1)) → p3)) ∨ ((((p5 → p5) ∧ (p4 ∨ False)) ∨ p1) ∨ ((True ∨ True) ∨ p3))) := by
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
theorem thm_5_vars_134045505237144081549743196896 : (((((p4 ∧ False) ∨ (((False ∧ ((True ∨ p3) → (False → ((p4 → True) ∧ p2)))) ∨ (p4 → p5)) → p3)) ∨ p3) ∨ True) ∨ ((p2 ∧ p1) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308598936521842116589526963246 : (p2 ∨ (((p4 ∧ (p5 → False)) → (((((False ∧ True) → (((((p1 ∨ p2) ∧ p2) ∧ False) → p4) ∨ p4)) ∨ p3) → (p2 ∧ True)) ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53969535205225406851988839600 : ((((p1 ∧ ((p5 ∨ (p2 ∧ False)) → (p2 → p5))) ∧ True) → ((((p5 → p3) ∨ (p2 → (((p4 ∧ True) → p3) ∧ p4))) ∨ p3) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339784494152804893500243648155 : (p1 → (p5 ∨ ((((p4 → (((p3 → ((p4 ∧ (True ∧ p5)) ∨ p2)) ∧ (True ∧ p4)) ∨ p4)) ∨ (p3 ∨ (p4 ∨ (p4 ∧ p5)))) → p2) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_871984044676566379820021312252 : ((((p4 ∨ (((p2 ∧ (p1 ∨ True)) ∨ False) ∨ ((((((p5 → (p1 ∨ True)) → False) ∧ p4) → p3) ∧ (False → (p3 → p3))) ∨ p1))) → False) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ (((p2 ∧ (p1 ∨ True)) ∨ False) ∨ ((((((p5 → (p1 ∨ True)) → False) ∧ p4) → p3) ∧ (False → (p3 → p3))) ∨ p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (p5 → (p1 ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h6
    -- False on the left can always be used.
    apply False.elim h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314225785660088640781996816123 : (p3 ∨ (((p4 ∧ ((p5 ∧ p5) ∨ ((True ∨ p5) → (((True ∧ (p2 ∨ (False → p2))) ∨ (True → p2)) → p3)))) ∧ p5) ∨ (p2 ∨ (False → True)))) := by
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
theorem thm_5_vars_42225762872751424933041643750 : (((False ∧ (((((p2 → p3) ∨ (p2 ∨ (p4 → (False → p2)))) ∨ (p5 → p1)) → ((p3 ∨ True) ∧ p5)) → (p3 ∧ (p3 ∧ p4)))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325170972458204552908845566803 : (p5 ∨ (True ∧ (p2 ∨ (((p2 → (p3 ∧ (((p5 ∨ False) → (p5 → p3)) ∨ p4))) → (((True ∨ p2) ∨ False) → ((False ∨ False) ∧ p2))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149351944017167654247248692996 : (((p4 ∨ True) → (p3 ∨ (((p2 → p3) ∧ (p3 → True)) → (p3 → ((p2 ∨ p2) ∨ (False ∨ (False ∨ p3))))))) ∨ (True ∨ ((p4 ∧ True) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233266664619702811315229097163 : ((True ∨ (p4 ∧ p1)) → (((False ∨ ((p2 ∧ p4) → (((True → ((True ∨ False) ∨ (True ∨ p4))) → p1) ∧ p2))) ∧ False) ∨ (p3 → (p4 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198745922361812482492620216558 : ((True → ((p1 ∨ ((p2 → p5) ∨ p3)) ∨ False)) ∨ ((((p5 → ((p3 → (p4 ∧ p5)) ∧ p3)) ∧ (False ∧ p5)) ∨ (p2 → True)) ∧ (True → True))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_886772284947866400351274765710 : ((((((False → p4) ∧ (False ∧ ((p2 ∨ p1) ∨ (p4 ∧ (((p4 ∨ False) ∨ (p2 ∨ p3)) ∨ (p1 ∧ (p2 ∨ p1))))))) ∨ True) → (False ∧ p5)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False → p4) ∧ (False ∧ ((p2 ∨ p1) ∨ (p4 ∧ (((p4 ∨ False) ∨ (p2 ∨ p3)) ∨ (p1 ∧ (p2 ∨ p1))))))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65699258669436955277815124038 : ((p4 ∨ ((p5 → (p4 ∧ (((False → (p5 → p2)) → False) ∧ (p1 ∧ ((p1 ∧ (((p2 ∨ False) → p3) → (p1 → False))) → p4))))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349846870453902090914445125162 : (p4 → ((p4 ∧ (((((False ∨ (((True ∧ p3) ∨ p1) → (False ∨ (p3 → (p2 ∧ p3))))) → p5) ∨ p4) → False) → ((p5 → p1) ∧ p3))) ∧ p4)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((False ∨ (((True ∧ p3) ∨ p1) → (False ∨ (p3 → (p2 ∧ p3))))) → p5) ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (((False ∨ (((True ∧ p3) ∨ p1) → (False ∨ (p3 → (p2 ∧ p3))))) → p5) ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655893405806836056037678764159 : (((((True → ((p2 ∨ (((((p1 ∨ (p3 ∨ p2)) → p5) ∧ True) ∨ p1) ∧ (p1 ∨ p1))) ∨ p2)) → ((p5 → p1) → p3)) ∨ (True ∨ p2)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_65769701682059016366891526451 : ((p4 ∨ (((p5 → ((p1 → p2) ∧ (p4 ∨ (p5 ∧ p1)))) ∧ ((p1 → p1) ∨ (p4 ∨ p4))) ∨ ((p1 ∧ ((False ∨ p3) → p3)) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672320042375802630717704467398 : ((((((p4 ∨ (p1 → ((p4 → (p2 ∨ ((((p4 → p2) ∧ p5) ∧ p3) → p1))) ∨ p1))) ∧ (p4 → p2)) → False) → ((p3 ∧ p5) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186940624734860926629705089306 : (((p3 → (False ∧ p3)) ∧ (p1 → (((False → p4) ∨ True) ∧ p1))) → ((((p2 ∧ p5) ∧ (p3 → (False ∨ (p5 ∨ p3)))) ∧ p4) → (p5 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135880538863006403069196259114 : (((p1 ∧ (((p5 ∨ p4) ∧ ((True ∨ True) ∨ p4)) ∧ (True ∨ p2))) ∨ (True → ((True ∧ p1) ∨ (p2 ∨ (p5 → p5))))) ∨ ((False ∨ p3) ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809309512036843495945807802199 : (((p5 → (((p4 ∨ p3) → ((((((p1 ∧ p5) ∧ p4) ∧ (p5 ∧ (False ∧ True))) → ((p1 → True) ∧ p1)) ∨ p3) → (p3 ∧ p5))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135884066155513354615153162164 : (((False ∨ ((True ∧ (((p3 ∨ p5) ∧ p1) ∨ p4)) ∧ (p3 ∨ p3))) ∨ (p3 → (((p1 → True) → (p1 ∧ p1)) ∨ p5))) ∨ ((p1 ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134170568084166833756044915290 : (((((((p1 ∨ p2) ∨ (False → p4)) ∧ p4) → (((p5 → False) ∧ False) ∧ p5)) ∨ (True → ((p2 → True) ∨ True))) ∨ p3) ∨ (p3 → (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256804821266627401072011151499 : ((p1 ∨ p2) → (p2 ∨ ((False ∨ (p1 → ((p5 → p1) ∧ ((p3 → p3) → p2)))) ∨ ((p4 → (p4 ∨ p4)) ∨ (((False → p5) ∨ p4) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



