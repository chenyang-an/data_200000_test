variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648845310562469181648977953764 : (((((p4 → ((((p4 ∨ p1) → p4) ∧ p1) ∧ (((True → (p3 → (p2 ∨ (p1 → (True → p4))))) → p3) ∨ p2))) ∨ p4) ∧ (p4 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179066419798941671738584232116 : ((True ∧ ((True ∨ (True ∨ (True ∧ ((False ∧ p5) → (p5 → p2))))) → p5)) ∨ (True ∨ (p4 ∨ ((p2 ∨ p3) ∧ (True ∧ ((p1 ∧ False) → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588732415490059017644057577798 : (((((p4 ∧ (((p4 ∨ (p4 ∨ p1)) ∨ ((((True ∧ True) ∨ (False → (True ∨ (True → (False → True))))) ∨ False) ∧ p4)) ∧ p3)) ∨ p1) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198259269481067519431324651690 : ((False ∧ ((True ∧ ((p4 ∧ p5) → p3)) ∨ p3)) ∨ ((p5 ∨ (p5 → ((p1 ∧ True) → (False ∨ p5)))) → (((p1 ∨ True) → False) → (p1 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p1 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116374428663257171219751582919 : ((((p4 ∨ False) → p1) → (p5 ∨ (((p3 ∧ p1) ∨ True) → (False ∧ ((((p2 ∧ p2) ∨ (p5 ∨ False)) ∨ (p5 ∨ False)) → p3))))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190463005192870101554701937182 : (((((p4 → (False ∨ (True ∧ p1))) ∧ True) ∧ True) → p3) ∨ (((p4 → False) ∨ (False ∧ ((((p1 ∨ p2) ∧ p3) ∨ False) → False))) ∨ (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184258934938568785107507036660 : (((((True ∨ p1) ∨ (p4 ∧ (True ∨ p4))) ∧ (False ∨ True)) → False) ∨ (p2 → ((p3 ∨ ((p1 ∧ False) ∨ (p1 ∨ ((p3 → p5) ∧ p4)))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172492223349592913441011454659 : (((p1 ∨ ((p1 ∨ False) ∨ p3)) → ((True → p2) ∨ (False ∧ ((p3 → p3) → p1)))) ∨ (p1 ∨ (p2 → ((((p3 ∧ True) ∨ False) ∧ p3) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56485978387788179338915987943 : (((True ∧ (True → (p5 ∨ p4))) → ((False ∨ p3) ∧ ((((p3 ∨ (p1 ∨ p4)) ∧ (p3 ∨ True)) ∧ ((p5 ∨ p1) ∧ (p4 ∧ p4))) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58192736258344209744361775517 : (((p3 ∧ p5) ∧ (((True ∧ ((p4 ∨ p4) → p2)) → (p5 ∧ (p4 ∧ (p4 ∧ (((True → (True ∨ p3)) → (p5 ∧ p2)) ∧ False))))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158353886799841278785237712007 : (((True ∨ p3) ∧ ((p2 → (p3 ∨ (p2 → (p3 ∨ ((p3 ∧ ((False → p3) ∧ p4)) ∨ False))))) ∧ False)) ∨ (p5 → (p4 ∨ (p5 ∨ (p2 ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653915536739814689802440053446 : ((((((True → True) ∧ (((p2 → p2) → False) ∨ (((p3 → ((p5 → ((p1 ∧ p3) ∧ p5)) ∧ True)) ∧ p5) ∧ p3))) ∧ p1) ∨ (False → False)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_862032600395081804870471868207 : ((((((p1 ∨ ((p1 → p4) → (((p1 ∧ True) ∨ (p2 ∨ (p3 ∨ p2))) ∧ (p5 ∨ p5)))) ∧ p4) ∨ ((False → p1) → (False ∨ True))) → p2) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ ((p1 → p4) → (((p1 ∧ True) ∨ (p2 ∨ (p3 ∨ p2))) ∧ (p5 ∨ p5)))) ∧ p4) ∨ ((False → p1) → (False ∨ True))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171879310821570166579011173640 : (((p5 ∧ ((True → p3) ∨ ((p1 → ((p1 ∧ p4) ∨ True)) ∧ (p1 ∨ p4)))) → p1) ∨ (((((p5 ∨ p2) ∧ (p4 → True)) ∧ True) → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184107186609284056167766651319 : ((((p1 ∧ p3) ∨ (p3 ∧ (False ∧ ((True ∨ False) ∨ p4)))) ∨ False) ∨ (((p2 ∨ p1) ∧ ((p4 ∧ (p5 ∨ False)) ∨ (False ∨ (p2 → p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218560764418294533255571360413 : (((False → p1) → (p3 → False)) → (((p3 ∨ (((p3 → ((p2 ∧ p4) ∨ True)) ∧ p2) ∧ p3)) ∧ (((p1 ∨ p3) → p5) ∧ p5)) ∨ (False → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42078252089247613773231822781 : ((((p1 → p4) ∨ (((p5 → p3) → p5) ∧ ((p4 ∨ p3) ∨ (p1 ∧ (p3 → (p2 → ((p4 ∨ ((p2 → True) ∨ False)) → p5))))))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64910356292915832853006902966 : ((p2 ∨ ((((p1 → ((((False → True) ∧ (False ∧ (p3 ∨ True))) → (p2 ∧ p1)) ∧ p5)) → p3) ∨ p3) → ((True → p3) ∨ (p2 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309953485691114459054966341252 : (p2 ∨ (((((True ∨ ((p2 → False) → (p4 → (p5 ∧ (p3 ∨ p3))))) ∨ p2) → (p1 ∧ p4)) → p1) → (p2 → (p1 → ((True ∧ p3) ∨ p1))))) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69242756082924474014133812223 : ((p5 → ((False → (True ∧ False)) ∧ (p4 ∨ (((p2 ∨ p3) → p3) ∨ (p1 → (p4 ∨ (((p2 ∨ True) → (True → (p5 ∧ p4))) ∧ p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259040379391311470971145628542 : ((True → p4) → ((False ∧ p5) ∨ ((p3 ∨ ((p3 ∧ p1) → False)) ∨ (p3 ∨ ((((p5 → p5) → ((p3 ∧ True) ∧ False)) ∧ p5) → (p3 ∧ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p5 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h5
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193282362380857675534839396712 : ((((True ∧ p2) ∨ True) ∨ ((p2 ∨ p3) ∨ (p5 ∨ True))) → (p5 ∨ (((((False → (p4 ∧ False)) ∨ p1) ∨ True) ∨ p5) ∧ ((False → p5) → True)))) := by
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
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
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
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
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
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
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
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
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
        -- Implications on the right can always be decomposed.
        intro h18
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115833528188315079679784951291 : (((True ∧ (False ∨ (p5 → p2))) ∧ (p1 ∧ ((((p3 ∨ p1) ∧ (p1 → p5)) ∧ ((p4 → True) → ((p2 ∧ p5) ∧ p5))) ∨ False))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165206521642152723193167842731 : (((((False → p4) ∧ (p2 ∨ (p2 → (p2 ∨ ((p4 → p3) ∨ p2))))) → p5) ∨ (True ∨ p3)) ∨ (((p3 ∧ True) → (p5 ∧ True)) ∨ (p2 → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354580282516539496991866036237 : (p5 → ((((((p1 ∨ p4) ∨ p1) ∧ p4) ∨ (((p4 ∨ (p5 ∧ True)) ∧ (False → (p4 → p2))) ∨ (p4 ∨ ((p2 ∧ p2) ∧ p2)))) ∧ p5) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44367748200877861696219085439 : ((((((p5 ∨ p2) ∧ True) ∧ (((p2 ∨ p3) → (p5 → p4)) ∧ (p5 ∧ p5))) ∧ (p1 ∧ (p4 ∧ (p1 ∧ (p1 ∧ (False → p4)))))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300138747486462562984246442955 : (False ∨ ((p1 ∧ (False ∧ ((((p5 → p1) ∧ (p4 ∨ False)) ∨ (True ∧ False)) → (True → ((p3 ∧ (False ∧ p3)) ∨ (p1 ∨ True)))))) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302886952877835243888065831627 : (False ∨ (True → ((p4 → (p1 → (False → (p4 → (p3 → p5))))) → (p4 → ((p5 ∧ (p4 ∨ p4)) ∨ (p2 ∨ ((False ∧ (True ∨ True)) → p2))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116380289251902067424859813054 : ((((p2 → p4) → p5) → (((True → p2) → ((p2 → p1) → (p3 ∨ False))) ∧ ((p3 → (p5 ∧ (p4 ∧ False))) ∨ (False ∧ p2)))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747466695615962684014972694333 : ((((True → False) → (False ∨ ((((p4 → (p5 → p1)) → (p2 → (((p3 → False) → p1) ∨ p3))) ∧ (p5 ∨ (p5 ∨ (True → False)))) → p1))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172165219324800108518395003209 : ((((p4 → (p3 → ((p2 → p1) ∨ p1))) ∨ (p3 ∧ p5)) ∨ (p5 ∨ (p1 → p2))) ∨ (((p5 ∨ (True → p4)) ∨ (False ∨ (p4 ∧ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726004740034717081478641499706 : (((((p5 → False) ∧ p3) ∨ ((True ∧ p4) ∧ (p5 → ((p1 ∨ (((p1 ∨ (p4 ∨ p3)) ∧ (True ∧ (p1 ∧ p4))) → (p3 → p5))) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234213795043923518079464094046 : ((False → (p4 ∧ p4)) → (((p2 ∧ ((True → p3) → (p4 ∧ p4))) → ((p1 ∧ ((p5 → p1) ∧ p3)) ∧ p5)) ∨ ((p4 → (p1 → p1)) ∨ p5))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39161725947098380914541071175 : ((((p3 ∨ p5) → ((False ∧ (p2 ∨ (((p2 → p1) ∨ (p2 ∧ (p4 ∧ p5))) → True))) ∧ (True → ((p3 → (p1 ∨ p3)) ∧ p1)))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148503264045333166482713505981 : (((p4 ∧ ((True ∨ p1) → ((False ∨ False) ∧ (True → (p3 → True))))) ∨ (((p1 ∨ (False → True)) ∨ p2) ∨ p2)) ∨ ((p3 → (False → False)) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57699117615506797088476487750 : ((((p1 ∧ True) → p1) → (((p1 ∨ ((((p4 → p1) ∧ p1) ∨ (p4 ∨ (p1 ∧ (True → (False ∨ p1))))) ∧ p5)) ∨ p3) ∨ (p1 → True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43931667589997263541101737940 : ((((((((p4 ∨ p3) ∨ (p4 ∨ (True ∨ (p5 ∨ p2)))) → (p5 ∨ (p5 → p2))) ∧ p1) → ((p4 → p5) → p3)) ∨ (False ∧ True)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_391411753284649250188619081127 : (((((p3 ∨ ((p1 → p5) → (p3 ∧ p2))) → (((p4 ∧ (False ∨ p2)) ∧ (p5 ∨ (((p3 ∧ (p2 ∧ False)) ∧ p4) ∨ p5))) ∧ p1)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_56348900898317287598798330983 : (((((p3 → False) → p1) ∨ p3) → (((p5 ∧ ((p4 ∨ p4) → p1)) ∧ ((((p5 ∧ p3) → p3) ∨ (p4 ∨ (p1 ∨ p2))) ∨ p5)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52930368605678292664524001119 : (((((True → (p2 ∧ p2)) ∧ (((p5 → p5) ∧ p3) ∧ False)) ∧ True) ∧ (((p5 → (False ∨ ((p3 ∧ p4) ∨ p2))) ∧ (False ∧ False)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148807976451521769212100478431 : ((((p5 → (p3 ∧ (p1 ∨ p3))) → p4) → ((p5 ∨ (p2 ∧ ((False ∧ (p3 ∨ p3)) ∧ p5))) ∨ (True → p1))) ∨ (p5 → (p2 → (p2 → p5)))) := by
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
theorem thm_5_vars_766803840950364100359314895077 : (((p4 ∧ (p3 ∨ (((((p3 ∨ (True ∧ (True ∧ p2))) ∧ True) ∧ p5) ∧ p4) ∨ (p2 ∧ (((p4 ∨ (p1 ∧ p2)) ∨ (p4 → True)) ∨ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145454693010471619230524911873 : ((((p3 ∨ p2) ∧ (p4 ∨ p1)) → ((((((p2 → p2) ∧ ((True ∨ False) ∧ p5)) ∨ p4) ∧ p2) ∨ True) ∨ p4)) ∧ (((False ∨ p3) → p3) ∨ p1)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h10
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137633632085221912113728037273 : ((False ∨ ((p1 ∨ (((((((True ∨ p5) → p5) ∨ (p4 ∧ False)) ∧ (p1 ∨ p3)) ∧ p5) → False) → p2)) → (p4 ∧ p4))) ∨ (True → (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42176900926887006640254569027 : (((True ∧ (((p3 ∨ p5) ∧ (((p4 ∨ (p5 ∨ ((p1 ∧ (True ∨ (p1 → (p4 → (True → False))))) → p4))) → p5) ∨ p4)) ∨ p5)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619328192503334551908280855357 : ((((((p2 → p5) ∨ p1) → (((p2 ∨ p3) → ((p1 ∧ p1) ∨ p4)) ∧ (p3 → (p4 ∨ (((p4 ∨ (p3 ∨ True)) ∨ p2) ∨ p1))))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_228128710482106037794798530478 : ((p4 ∧ (False → p3)) ∨ (((((((((p4 ∨ (False → True)) ∧ p1) → ((False ∧ p2) → p1)) ∧ False) ∨ p2) ∧ p4) ∨ p3) → p2) → (p3 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((((((p4 ∨ (False → True)) ∧ p1) → ((False ∧ p2) → p1)) ∧ False) ∨ p2) ∧ p4) ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119418475902925879302585805947 : ((p4 → ((p2 ∨ ((p3 ∨ p4) → (((p3 ∧ p3) → (((True ∧ p5) ∧ p1) ∨ ((p5 → (p4 → False)) ∨ False))) ∧ True))) → p5)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43135007893912282889627439605 : ((((((True ∧ (p2 ∨ ((False ∨ p5) → p4))) → (p3 ∧ True)) ∨ (((p1 → p4) → (p4 ∨ ((True → True) → p1))) ∨ p5)) ∧ p3) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752665488155842708509160257089 : (((False ∧ (((p4 ∨ ((((p3 ∨ p1) ∨ (False → ((p2 ∧ p3) ∨ (((p5 ∨ p1) ∧ False) ∨ p3)))) ∨ True) ∧ p2)) ∨ (p3 ∨ False)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312595876440472924872722783921 : (p3 ∨ (((p4 ∧ (p2 ∧ ((False → (p1 → (p4 ∨ True))) ∧ (((False → (p4 → ((False ∧ p4) ∧ True))) ∧ (p2 ∧ False)) ∨ True)))) ∨ True) ∧ True)) := by
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
theorem thm_5_vars_117311267830383978815920783838 : ((False ∧ (((p5 → True) ∧ ((True ∧ True) ∧ (False ∨ ((False ∨ p5) ∧ ((p2 ∨ False) ∧ False))))) ∨ (((True → True) ∧ False) → p1))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179485804409241908597183950835 : ((True → ((p3 → p3) ∧ ((p3 ∧ ((True ∨ p2) → (p3 → p2))) ∧ p4))) ∨ ((p5 ∨ ((False ∧ p5) ∧ ((p4 → p3) → (p1 → p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231309651568850359943391984632 : (((True → True) ∨ p1) → ((p4 ∧ (((((((p5 → p2) ∨ p2) ∨ p3) → (True → (p5 → (False → p4)))) → (p5 → p1)) ∧ False) ∨ p1)) ∨ True)) := by
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
theorem thm_5_vars_350020711272287011620192638576 : (p4 → (((((((p5 ∨ ((p2 ∨ p2) ∨ ((((p1 ∨ (p3 ∨ p3)) ∨ p2) → (True ∨ p2)) ∧ p3))) ∨ p5) ∧ True) ∧ True) → p4) → p3) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112463410732747755802169978698 : (((((((p4 ∧ (p3 ∨ ((p2 ∨ p1) → False))) ∨ p4) ∧ p4) ∨ ((((p3 → p1) ∧ (p4 ∨ False)) → False) ∨ p4)) ∨ p3) → p1) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186336145908386767408571051545 : ((((((p1 ∨ p1) ∧ False) ∨ p1) → (p3 ∨ (p2 → p1))) → False) → ((((p2 ∧ p4) ∨ p2) ∧ (False → (True → ((p4 ∨ p3) ∧ p2)))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 ∨ p1) ∧ False) ∨ p1) → (p3 ∨ (p2 → p1))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h6
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307758580229568098024567155020 : (p1 ∨ (p3 → (((p2 → p3) → p2) → (((p5 ∧ ((p5 ∧ p5) ∧ (p3 ∨ (p1 ∧ (p1 → True))))) → ((p5 ∨ p3) ∧ (p1 ∧ p2))) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p2 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90920339142248788952010212902 : (((True → False) ∧ (((True ∧ (((False ∧ (False → p2)) ∨ p1) ∧ (p4 ∨ ((True ∨ (p3 → p4)) ∨ p3)))) → p2) ∨ (False → (True ∨ False)))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299317877322965067585211665466 : (False ∨ ((((p1 ∨ p4) ∨ ((p5 ∧ p2) ∨ p1)) ∨ (False → (p1 ∨ ((p2 → p1) ∧ ((False → (True → p2)) → ((True ∧ p3) ∨ p3)))))) ∨ False)) := by
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
theorem thm_5_vars_609334332115626190027335417204 : ((((((False ∧ p1) ∨ (p3 → (((p1 → ((((p3 ∨ p5) ∧ (p4 ∧ (p2 → False))) ∨ (p2 ∨ p3)) ∧ False)) ∧ p3) ∨ False))) ∨ p1) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608869800881455581236753219578 : (((((((p5 ∨ ((False ∨ (((False → (p3 → False)) ∧ p2) → p2)) ∨ (True ∧ p1))) ∨ False) → (p4 ∨ (p1 ∨ (False → p3)))) ∨ True) ∨ p4) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116069289484104458243635313443 : ((((p4 ∨ p1) ∧ True) ∧ (p3 ∧ (((True ∨ ((p3 ∧ (p3 → p2)) ∨ p1)) ∨ (p1 → (True → (p3 → p3)))) → (p3 → p4)))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62896152339341052324394879308 : ((p4 ∧ ((p2 ∨ p4) ∨ ((((p4 ∧ True) → ((p2 → ((p1 → (p2 ∨ p1)) ∨ (False → p2))) ∨ p4)) ∧ (p4 ∨ p4)) ∧ (p5 ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199405636403098865297403989010 : ((((False ∧ p4) ∨ (p5 ∧ (p2 ∨ p1))) ∨ p2) → (True ∧ ((((p4 ∧ (((p3 ∧ (p4 → p4)) → True) ∧ (p3 ∨ p3))) ∧ p5) ∧ p1) ∨ True))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- False on the left can always be used.
      apply False.elim h4
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260965510087194772854469278104 : ((p4 → p1) → (((False ∨ (((False ∨ ((p2 ∨ p2) ∨ p2)) → p5) ∧ (((p4 → p4) ∨ True) ∨ (p5 ∨ p2)))) ∨ p2) ∨ (True → (True ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167975520969284707742576007858 : ((((True → (False ∧ (False ∨ p3))) ∧ p3) ∧ (True ∨ ((p2 ∨ True) ∨ ((p3 ∨ p3) ∨ p5)))) → (((((p5 ∨ p4) ∧ p4) → p5) → p2) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h15 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h16 := h5 h15
        -- We need to get the left conjuct of h16 based on <expert-advice>.
        let h17 := h16.left
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h21 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h22 := h5 h21
          -- We need to get the left conjuct of h22 based on <expert-advice>.
          let h23 := h22.left
          -- False on the left can always be used.
          apply False.elim h23
        case inr h24 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h25 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h26 := h5 h25
          -- We need to get the left conjuct of h26 based on <expert-advice>.
          let h27 := h26.left
          -- False on the left can always be used.
          apply False.elim h27
      case inr h28 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h29 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h30 := h5 h29
        -- We need to get the left conjuct of h30 based on <expert-advice>.
        let h31 := h30.left
        -- False on the left can always be used.
        apply False.elim h31
  -- Conjunctions on the left can always be decomposed.
  let h32 := h1.left
  let h33 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h34 := h32.left
  let h35 := h32.right
  -- Disjunctions on the left can always be decomposed.
  cases h33
  case inl h36 =>
    -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
    have h37 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h34, we can now drive its conclusion.
    let h38 := h34 h37
    -- We need to get the left conjuct of h38 based on <expert-advice>.
    let h39 := h38.left
    -- False on the left can always be used.
    apply False.elim h39
  case inr h40 =>
    -- Disjunctions on the left can always be decomposed.
    cases h40
    case inl h41 =>
      -- Disjunctions on the left can always be decomposed.
      cases h41
      case inl h42 =>
        -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
        have h43 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h34, we can now drive its conclusion.
        let h44 := h34 h43
        -- We need to get the left conjuct of h44 based on <expert-advice>.
        let h45 := h44.left
        -- False on the left can always be used.
        apply False.elim h45
      case inr h46 =>
        -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
        have h47 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h34, we can now drive its conclusion.
        let h48 := h34 h47
        -- We need to get the left conjuct of h48 based on <expert-advice>.
        let h49 := h48.left
        -- False on the left can always be used.
        apply False.elim h49
    case inr h50 =>
      -- Disjunctions on the left can always be decomposed.
      cases h50
      case inl h51 =>
        -- Disjunctions on the left can always be decomposed.
        cases h51
        case inl h52 =>
          -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
          have h53 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h34, we can now drive its conclusion.
          let h54 := h34 h53
          -- We need to get the left conjuct of h54 based on <expert-advice>.
          let h55 := h54.left
          -- False on the left can always be used.
          apply False.elim h55
        case inr h56 =>
          -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
          have h57 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h34, we can now drive its conclusion.
          let h58 := h34 h57
          -- We need to get the left conjuct of h58 based on <expert-advice>.
          let h59 := h58.left
          -- False on the left can always be used.
          apply False.elim h59
      case inr h60 =>
        -- One of the premise coincides with the conclusion.
        exact h60



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116290413983665980235115344819 : (((p4 ∨ (False ∧ p5)) ∨ (p5 ∧ (((p4 ∧ p2) ∨ True) ∨ (((p3 → ((True → (p3 ∧ (p1 → p2))) ∧ p3)) ∨ True) → p1)))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147676496986037617096602912496 : (((((p5 → ((p4 ∧ ((p3 ∨ False) → ((True ∧ p3) → p4))) → p4)) ∨ p5) ∧ (p1 → (p2 ∨ True))) → p5) ∨ ((True → False) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113435048696990239215898225834 : (((((p3 → ((p2 ∧ (((((True → p3) → p5) ∧ p2) ∧ True) ∧ p3)) → (p3 ∧ (p1 → p5)))) → p5) ∨ p4) ∨ (True → p3)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135801483418770563255883384429 : (((p4 ∧ (((True ∧ p5) → p2) ∨ ((((p2 ∧ False) ∨ True) ∧ p2) ∧ p4))) → ((p5 ∨ False) → ((False ∨ p3) ∧ True))) ∨ (p3 → (p3 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171767582546261523764136777870 : (((((p1 ∧ True) ∨ ((p3 ∧ ((False → True) ∧ True)) → (p5 → False))) → True) → p5) ∨ ((p2 → (((False ∨ (p3 → p4)) ∧ p2) ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135231728890955096675491256369 : ((((p4 → (((p1 → p1) → False) ∨ p1)) → (p1 → (((p2 ∧ ((False → p1) ∨ True)) ∧ p5) ∧ p5))) → (True → p4)) ∨ (p1 ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67482833895124383442058128539 : ((p1 → ((((((p1 ∨ False) → p1) ∨ (p2 ∧ (True ∨ p2))) ∨ (False → p4)) → True) → (((((p2 → p4) ∧ p4) ∧ p1) ∨ p2) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200320637603773756475847332828 : (((True ∨ True) ∧ ((p2 ∧ p3) → (p2 ∨ p2))) → ((((((p1 → ((p5 ∨ p5) ∧ p1)) → p2) ∨ (True ∧ False)) ∨ p2) ∨ p4) ∨ (True ∨ p5))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313141532692380537461724136785 : (p3 ∨ (((((False ∨ (p3 ∨ ((p4 ∧ True) ∧ False))) ∨ (p5 ∧ (False → (p2 ∨ p5)))) → p2) → (p3 → (False ∨ ((p1 ∧ True) ∧ True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148674952933781317472202804450 : (((((((False ∨ p4) → p4) → p2) ∨ p2) → p5) ∨ ((((p5 ∧ p4) ∧ p1) ∧ p1) ∧ ((p3 → p4) → False))) ∨ ((p5 → (False → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115129774600870423207729408878 : ((((p4 → ((p1 → p1) → True)) → (p5 → (False → (p2 → True)))) → ((p1 ∧ (p4 ∨ (True ∨ ((True → p3) ∧ p2)))) ∧ p5)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690776624036738316286351137926 : ((((((False ∧ (True → ((p1 ∨ False) ∧ (p4 ∧ p5)))) ∨ ((False ∨ p5) ∧ False)) → p3) → ((((p3 ∨ p5) ∨ p1) → (p1 ∧ True)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47998528564783446820249730511 : (((((p4 ∧ (False ∨ ((p1 ∧ False) ∧ p2))) ∧ (True → ((p5 ∧ p1) ∨ p5))) ∨ ((p2 → ((p3 → p4) ∨ p1)) ∨ p4)) → (p3 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200357994497911233302112411359 : (((False → p2) ∧ (((p1 ∧ p3) → False) → True)) → ((((True → (p4 ∨ p3)) → p4) ∨ ((False ∨ (p2 ∧ (p4 ∧ False))) → (True → p4))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204211992004902407064984158500 : ((((False ∧ (True ∨ p3)) → p3) ∧ False) ∨ ((p2 ∧ (p2 ∨ ((p3 ∨ p4) ∧ False))) → (((((p3 ∧ True) ∧ (p4 ∧ p1)) ∧ p2) ∨ p1) ∨ p2))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142414721643594263913298594109 : ((p4 ∧ ((p2 → p5) ∧ ((p4 ∧ (p2 ∧ False)) → (False ∨ (((p2 → p1) → (False ∧ (p1 ∨ False))) ∨ (False ∧ p2)))))) → ((p1 ∧ p2) → p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246134186591885849912857145622 : ((p4 ∧ p2) ∨ (((p3 → p2) ∧ (((p5 ∧ True) ∨ (((False ∧ (p4 ∨ False)) ∧ (p3 ∧ ((p1 → p4) → (p2 → p2)))) ∧ p4)) ∨ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227700416629738652724564960791 : ((p1 ∧ (p1 ∧ p2)) ∨ ((p1 ∨ ((p5 ∨ (((p2 ∧ p4) ∨ p1) ∧ ((p2 → (p2 → p1)) ∧ ((p5 ∧ (p4 ∨ True)) → p4)))) ∨ True)) ∨ p4)) := by
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
theorem thm_5_vars_41010441782190068671641568599 : ((((((p3 ∨ (((p2 → (p4 → ((p4 ∨ p2) ∧ p5))) ∨ p3) ∧ (p2 → ((p1 ∧ False) ∨ p3)))) ∧ p4) ∨ True) → (p1 → p3)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617223769157563158951493915516 : ((((((p1 → p2) ∨ ((False ∧ (p2 ∧ p5)) ∨ False)) ∨ ((((((False → p5) → p5) ∨ False) ∨ p3) ∨ (False ∧ (p1 ∨ p3))) ∨ p1)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49564104815354611063258407052 : (((((p5 ∧ (((p5 ∧ (p1 ∨ p5)) ∨ False) → ((False ∨ p3) ∧ p5))) → (True → p2)) → ((p3 ∨ p1) ∨ True)) → (p3 → (p2 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317025398176474257136328016221 : (p3 ∨ (p3 → (p4 → ((((p3 ∧ p4) ∧ (((p2 → ((p3 ∧ (False ∨ False)) ∨ (p2 ∧ False))) → p4) → (p1 ∨ p1))) ∧ p4) → (False ∨ p1))))) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h10 : ((p2 → ((p3 ∧ (False ∨ False)) ∨ (p2 ∧ False))) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h12 := h7 h10
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225135472838347773018340787696 : (((p3 ∧ False) ∧ p1) ∨ ((p2 ∨ (True → ((p4 ∨ p1) ∨ (True ∧ (False → (((False ∧ True) → (p2 → (True ∧ p1))) ∧ (True → p2))))))) ∨ p1)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230678087461401770287418905484 : (((p3 → p5) ∧ p5) → (p2 → (p5 ∧ (((True → (p4 ∧ (((p3 → False) ∨ p5) ∧ (p1 ∨ (p2 ∨ p2))))) ∨ (True ∨ (p3 ∧ False))) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703027728765113169582258477551 : (((((p3 ∧ p3) ∧ (((False ∨ p5) ∧ (False → p1)) ∧ p1)) ∨ ((p3 ∨ ((p2 ∨ p5) ∨ p2)) ∨ ((False → (False ∨ p4)) → (True → True)))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199358635032176190872318366659 : (((((p3 → p2) ∨ p2) ∧ (p4 → p5)) ∨ p1) → (True → (True → (((((p2 ∨ True) ∧ p4) → (True → (p5 ∨ False))) ∧ True) ∨ (p2 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h13 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h14 := h6 h13
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h16 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h17 := h6 h16
        -- One of the premise coincides with the conclusion.
        exact h17
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110742795489514494053178032959 : ((((((p2 ∧ p4) ∨ p2) ∨ ((p1 → (p5 ∧ (((p3 ∧ p1) ∧ (p5 → (False ∧ (False → False)))) ∨ p5))) ∧ p1)) ∧ p2) ∧ p2) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177629013973280459210812188085 : (((((p5 → (((p1 ∧ p1) ∨ (False ∧ p4)) ∨ p1)) ∨ p3) ∧ p2) ∧ p5) ∨ (((True ∨ p4) ∨ p2) ∨ ((False ∨ (p1 → (False → p1))) ∧ p3))) := by
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
theorem thm_5_vars_177752027207134059998611004721 : ((((p2 → p5) ∧ (False ∨ (p5 ∨ (p5 → (p2 ∨ (p2 ∧ p2)))))) ∧ p3) ∨ ((p1 → (p1 → (p4 → (p1 ∨ (p5 → p1))))) ∨ (p4 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152477335135072795771005714182 : ((((p5 ∧ p1) ∧ True) ∨ ((p1 ∧ p5) ∧ (p4 → (p1 ∧ ((((p3 ∨ p3) → p2) ∨ (p5 ∧ p1)) → True))))) → ((p1 → False) → (p4 ∧ p4))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h15 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h16 := h2 h15
    -- False on the left can always be used.
    apply False.elim h16
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h22 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h21
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h23 := h2 h22
    -- False on the left can always be used.
    apply False.elim h23
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- Conjunctions on the left can always be decomposed.
    let h27 := h25.left
    let h28 := h25.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h29 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h27
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h30 := h2 h29
    -- False on the left can always be used.
    apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190801356843860085082753017066 : ((((p1 ∧ p4) ∧ ((True ∧ p4) ∧ p4)) ∨ (p5 → False)) ∨ ((p4 → ((((p3 → p1) ∨ p5) → p4) ∨ ((p1 ∧ (p3 → p4)) → p2))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63212682256925182457320188687 : ((p5 ∧ ((p1 ∧ ((p5 ∨ (True ∧ (p4 ∧ ((p2 → p2) ∨ (p2 ∧ False))))) ∨ ((p2 ∨ p4) ∨ p3))) → (((p2 ∨ p5) ∨ p1) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134647733006938639785237981166 : (((((False ∨ ((False ∧ (True → (True ∧ False))) → p3)) → (p4 → p4)) ∨ ((p2 ∨ True) ∧ (p1 ∨ (p3 ∧ p2)))) → p2) ∨ (True ∨ (p5 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



