variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47449630997811677637487809837 : (((p3 ∧ (p3 → (((False → ((p1 → p1) ∧ (p5 → (p3 → (p4 → p1))))) ∨ ((p2 ∧ p2) ∧ (p5 ∧ True))) → p4))) ∨ (p3 → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113392548787916663517657511213 : (((p1 → (((p2 ∨ p4) ∨ ((p2 ∨ ((True → (p5 ∧ (True → True))) ∧ (p4 → p5))) ∨ p4)) ∨ (p5 ∧ p2))) ∧ (p5 ∨ p4)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765860099943204805307018584957 : (((p4 ∧ (((p4 → p5) ∨ ((p2 ∨ p1) → p2)) ∨ (p5 ∨ (((p2 ∨ p3) ∧ ((((p2 ∧ p2) ∨ p3) → p1) ∧ True)) ∧ (p3 → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307649082333077143178793667820 : (p1 ∨ (p1 → (False ∨ ((((p2 → False) ∨ ((False → p3) ∨ ((p3 ∨ (p1 → (p4 ∨ p4))) ∧ True))) ∧ p2) → ((p5 ∨ (p2 ∨ p2)) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172605350450988265391345090914 : (((p2 ∨ (False ∧ False)) → (((p4 ∨ ((True ∧ (p3 ∨ p3)) ∨ True)) ∧ p1) ∨ p4)) ∨ (False ∨ ((p2 → (p5 ∨ (p5 → True))) → (p1 ∨ True)))) := by
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
theorem thm_5_vars_112821628031090568304395763351 : ((((p2 ∨ (p5 ∨ (p1 ∨ p2))) ∧ (((False ∧ p1) → p1) ∨ ((((p2 → p4) ∨ p2) → p4) ∧ ((True ∨ p3) ∨ False)))) → False) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65513733468851009289676431695 : ((p3 ∨ (False ∨ (p5 → ((((((False ∨ True) → p4) → (p1 → p2)) → False) → (((p3 → (p4 ∧ p4)) ∧ p4) → (True → p4))) ∧ True)))) ∨ p5) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192991870731648575038438577328 : (((((True ∧ (False → p3)) ∨ p2) ∨ p5) → (False ∨ False)) → (((p5 ∧ (((p2 ∨ p1) ∨ p2) ∧ True)) ∧ ((p2 ∧ False) ∧ (p5 ∨ p3))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True ∧ (False → p3)) ∨ p2) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206062348512298361875469429263 : ((p3 ∧ (((p3 ∨ p5) ∨ p4) ∨ p4)) ∨ (((p2 → ((p3 ∧ p5) ∨ p1)) → (p4 → p4)) ∨ (False → ((True → p1) ∨ ((p2 → p5) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344300306014005303089676015858 : (p2 → (p3 ∨ (((p1 ∨ True) → (p5 ∨ ((((p3 ∨ p3) → (p4 → p5)) ∧ (((p2 → p1) ∧ (True ∨ p5)) ∧ p2)) ∧ p5))) → (False ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165167622109194297711593685847 : ((((True ∨ False) → ((p1 ∨ (p3 ∧ p2)) ∧ ((p1 ∨ (False ∧ p3)) → p2))) ∧ (False ∨ p1)) ∨ (((((True ∨ False) ∨ p1) → p4) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55504332329035984500346407538 : ((((False ∨ True) ∧ ((p5 ∧ p5) → True)) → (True ∧ ((p4 → ((p1 ∧ p3) ∨ (((p3 ∧ p4) → (p3 → False)) ∧ (p3 → p5)))) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226166761973552276925450293483 : (((p1 ∨ p1) ∨ p3) ∨ (p4 → (p5 ∨ ((True → p1) ∨ (False ∨ (True ∧ (p4 ∨ (((p5 ∨ p1) ∨ p5) ∧ (p4 ∧ (p2 ∧ (p5 ∧ p3))))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148975990293246824159732154010 : (((True ∧ (False ∧ p5)) ∧ (True → ((p2 ∧ ((p3 ∨ (p4 ∨ False)) ∨ p4)) ∨ (((p2 ∧ True) ∨ p2) ∧ p1)))) ∨ (p2 → ((p1 ∧ False) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18957846925249736418685199604 : (((p5 ∨ (((p4 ∨ p3) ∨ (p5 ∨ p4)) ∨ (((p3 ∨ (False ∨ p1)) ∨ p2) ∧ (p3 ∧ p3)))) ∨ ((True ∨ p1) → ((True → True) ∨ p2))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308369627342377187510611288650 : (p2 ∨ ((((False ∨ (((p5 ∧ (p4 ∧ (p2 ∧ p1))) ∨ p5) ∧ (True ∧ (((p3 → p1) ∨ (p2 ∨ False)) → (False ∧ p4))))) ∧ p4) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113506430061136444714390887145 : (((((p5 → False) ∨ (((True ∧ (p2 ∧ (p2 ∨ True))) ∨ (p1 ∨ p4)) → p5)) ∨ (False ∨ (p2 ∨ (p2 ∨ True)))) ∨ (p1 ∨ p1)) ∨ (False ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_622811677016309122247360524839 : ((((p4 ∧ (p5 → (p3 ∧ (((((p1 ∨ ((((p5 → p5) ∨ p2) ∧ p2) ∨ (p2 ∧ False))) ∨ p2) ∨ p1) ∨ (False → p3)) → p2)))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_48319564995737250247799085004 : (((False ∨ (p5 ∨ ((p3 ∨ (True → (((True ∧ (True → ((False ∨ (False ∨ p1)) → p5))) → (p3 ∧ True)) ∨ p2))) ∨ p4))) → (p2 → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687322602388904924493519434666 : ((((((p2 ∧ p2) → ((((False ∨ (p5 ∧ p1)) ∧ (p3 ∧ p3)) ∧ p2) ∧ p1)) ∧ True) ∧ (((p3 ∨ p3) ∧ p3) ∧ ((False ∧ True) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180810085106758450481469677657 : ((((True ∧ p4) → p3) ∧ ((((p1 → p5) ∧ (p2 ∧ p4)) ∨ p5) ∧ p2)) → ((((p1 ∨ p4) ∧ ((p5 → p1) ∨ p5)) ∨ (p5 ∧ False)) ∨ p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52718076062908166092530331711 : ((((((p3 → (False ∨ (p5 → p3))) → p2) ∧ (False → (p2 ∨ p5))) ∧ p1) → (True → (p4 ∧ (True ∧ (p3 ∨ ((p3 ∧ p3) ∧ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618099525344311761535453534628 : ((((((p5 → True) → (False ∨ p4)) ∧ ((p1 ∧ (p2 ∨ ((p5 → (p4 → p2)) → ((p3 ∧ p1) ∧ ((p3 ∧ p5) ∨ True))))) ∧ p2)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46216777755564793599627963390 : (((((True → ((p1 ∧ False) ∨ p4)) ∧ (p2 → (p5 → ((p3 → ((p3 → (False → p3)) → p2)) ∨ False)))) ∧ (False ∧ False)) ∧ (False ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670839656587411050948667748366 : ((((p2 ∧ ((((True → ((p4 → True) → (p4 → p5))) → (p1 → (False ∨ (p2 → True)))) ∨ (p3 ∧ p4)) → False)) ∨ (False ∧ (p2 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696148584862744612974730756058 : ((((p1 ∨ (((p1 ∨ (p1 ∨ p4)) ∨ (p2 ∨ (p2 ∨ (True ∧ p5)))) ∧ p4)) → (((p2 ∨ (True → p4)) → (p2 ∨ (p2 ∧ p1))) ∨ True)) ∨ p4) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
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
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114824794219682943303412574016 : (((False ∨ ((False ∨ ((False → (p3 ∨ p5)) → p3)) ∧ ((p2 ∨ p4) ∧ p4))) ∧ (((p5 ∨ (p3 ∨ (True → False))) → p3) ∨ p3)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117864833401894365841712618639 : ((p5 ∧ (((True → ((((True ∧ p1) ∧ ((p2 → p3) → p3)) → p2) ∧ ((p3 → ((True ∨ True) ∧ p5)) → False))) ∨ p1) ∨ False)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263818791766293912617355826567 : (True ∧ ((((p4 ∨ True) ∧ ((((p3 → p5) → p5) → (False → True)) ∨ (False → p1))) ∧ p4) → ((p5 ∨ (p1 ∨ (p1 ∨ (p4 ∨ False)))) ∧ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h18 =>
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h20 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h21 =>
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115190164466221739834647352827 : (((((p5 ∧ True) ∨ (True ∨ True)) → ((p3 ∨ p1) ∨ p2)) ∧ ((((True ∧ p3) ∧ False) → (p1 → (True ∧ p4))) ∨ (p5 ∨ p2))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138635438341065144321412548383 : ((((True ∨ (((p5 ∨ (False → p5)) ∧ p5) ∨ ((p3 ∨ (True ∨ p4)) ∨ ((p5 → p4) ∧ p3)))) → (p5 ∧ False)) ∧ p2) → (p1 ∨ (False ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ (((p5 ∨ (False → p5)) ∧ p5) ∨ ((p3 ∨ (True ∨ p4)) ∨ ((p5 → p4) ∧ p3)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198462810116945872018534920462 : ((p5 ∧ ((p3 → p1) → (p3 → (p5 ∧ False)))) ∨ ((p2 → ((False ∨ p4) ∧ p3)) ∨ (False → (((True ∧ p3) → (p2 ∨ (p4 ∧ True))) → p2)))) := by
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
theorem thm_5_vars_69255019295258243087411110091 : ((p5 → ((p5 ∨ (True → p2)) → (p3 → ((((((True ∧ ((p3 → p5) ∧ p3)) ∧ (p4 → True)) ∧ p1) → p5) → p4) ∨ (p5 ∨ p2))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136862025944813675917610663067 : (((p5 ∧ p5) ∨ ((p5 ∨ (((p3 ∧ (p5 ∨ ((False → (False ∧ p2)) ∧ True))) ∧ p3) ∧ (True ∧ (p1 → True)))) ∧ p1)) ∨ ((p1 ∧ False) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304010826328686905517322748564 : (p1 ∨ (((p5 → p1) → ((((((True ∨ p1) ∧ p4) ∨ ((True ∨ p1) ∧ (p3 ∨ p1))) ∨ p3) → (p3 → ((p5 ∧ p4) ∨ False))) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197173242776979797213647934753 : ((((((p5 ∧ True) ∨ p5) ∨ False) ∧ p5) → False) ∨ ((p4 → ((((p5 ∨ (((True ∧ p1) ∧ True) ∨ False)) ∨ p2) ∧ p4) ∨ (True ∧ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603277018335982109422992079188 : ((((p2 ∨ ((p3 ∧ p2) → ((p5 ∨ (False → (((p5 ∨ p2) ∨ (False → False)) → ((False → (True ∨ p3)) ∨ (p3 → True))))) → p4))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307466899770424086241511268979 : (p1 ∨ (p5 ∨ (False ∨ ((True ∨ ((((True ∧ p1) → (True ∨ (p2 ∨ (p1 ∨ p4)))) → (p2 ∧ p5)) ∨ p5)) → ((p2 ∨ (p5 → p5)) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229825135562641322352629971760 : ((p5 → (p1 ∧ p1)) ∨ (((p4 ∨ (False ∨ p2)) ∨ (p5 ∧ (p2 → ((p4 ∨ True) ∧ (((p4 ∨ True) ∧ p2) → ((False ∨ p5) → p1)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616065253813605094802148050884 : (((((p2 ∨ ((p5 → ((p1 → (p2 ∨ (p3 → (p4 ∧ True)))) → p1)) ∨ p5)) → (True → (((True → p5) → (p1 ∨ p5)) ∨ p4))) ∨ False) ∨ p5) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315144826797855200900148666406 : (p3 ∨ ((((p3 ∧ True) ∨ (True ∨ p2)) ∧ p5) → (((p2 ∧ ((False ∨ (p3 ∨ p3)) → ((True ∨ (False ∨ (p4 ∧ p1))) ∧ p1))) ∧ p3) → p1))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h12 : (False ∨ (p3 ∨ p3)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h13 := h6 h12
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h17 : (False ∨ (p3 ∨ p3)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h18 := h6 h17
      -- We need to get the right conjuct of h18 based on <expert-advice>.
      let h19 := h18.right
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h21 : (False ∨ (p3 ∨ p3)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h22 := h6 h21
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- One of the premise coincides with the conclusion.
      exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147416425946709354477334696854 : (((((p5 → p4) ∧ (True → p5)) → (((((True → p1) → p1) ∧ (True → (p1 ∧ p1))) → False) ∨ p4)) ∨ p3) ∨ (True → ((True ∧ p5) ∨ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225400925364337529910106780373 : (((p2 ∨ p5) ∧ p2) ∨ ((p4 → (p5 → False)) ∨ (p4 ∨ ((True ∨ (((True ∧ p5) → (((p2 ∨ p5) → False) ∧ (p2 ∧ True))) ∨ p1)) ∨ p1)))) := by
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
theorem thm_5_vars_154251594399982129245417028054 : ((((p2 ∧ ((p4 ∧ p2) ∨ p2)) ∨ ((((p1 ∧ ((True ∨ p1) → False)) ∨ True) ∨ p4) ∧ True)) ∨ False) ∧ ((p4 ∨ p1) ∨ (False → (p3 → p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148423540657989667853898190063 : (((((p3 ∧ (p1 ∨ (p4 ∧ False))) ∨ p2) → (p4 ∨ (False → (p1 ∧ p1)))) → ((p5 → p2) → (p1 → p5))) ∨ (((p1 ∨ False) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_978328516705883698277476669780 : (((True ∧ (False ∨ (((p1 ∨ True) → (p1 ∨ (((((p1 → (p5 ∧ (False → True))) → True) ∨ p1) ∨ (p1 → False)) → False))) ∧ (p5 → p4)))) → p1) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : (p1 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : ((((p1 → (p5 ∧ (False → True))) → True) ∨ p1) ∨ (p1 → False)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h14 := h11 h12
      -- False on the left can always be used.
      apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249138827759452691819318456326 : ((p4 ∨ p2) ∨ ((p5 → (p2 → p4)) ∨ ((((p1 → False) ∧ p1) ∧ (True ∨ (p4 ∧ p2))) → (p5 ∧ (((True ∨ (p4 → False)) ∧ p3) → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h12 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h12
    -- False on the left can always be used.
    apply False.elim h13
  -- Implications on the right can always be decomposed.
  intro h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h14.left
  let h16 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h1.left
    let h19 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h22 =>
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h23 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h24 := h20 h23
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- One of the premise coincides with the conclusion.
      exact h27
  case inr h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h1.left
    let h30 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h31 := h29.left
    let h32 := h29.right
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h33 =>
      -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
      have h34 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h32
      -- We have shown the premise of h31, we can now drive its conclusion.
      let h35 := h31 h34
      -- False on the left can always be used.
      apply False.elim h35
    case inr h36 =>
      -- Conjunctions on the left can always be decomposed.
      let h37 := h36.left
      let h38 := h36.right
      -- One of the premise coincides with the conclusion.
      exact h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342691687689501033489193421488 : (p2 → (((((p2 → p4) ∧ p2) ∨ p4) ∧ (p3 ∧ (p1 ∧ p1))) → ((False ∧ ((p5 ∧ True) → (p4 → (False ∧ True)))) ∨ ((p1 ∨ p4) ∨ p3)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h4.left
    let h9 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h4.left
    let h14 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126997096593154719316625186072 : ((True ∨ (p1 ∨ ((p2 ∨ ((False ∨ (True ∧ ((False ∧ p3) ∧ p1))) → (False ∧ p2))) ∨ ((p5 ∨ ((p1 ∨ p4) ∧ p3)) → p3)))) → (p5 ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124053286004745314511413730875 : ((((p1 → (((p3 ∨ p4) ∧ p4) ∧ p4)) → (p2 ∨ (False → False))) → (((p1 ∧ (True → (False ∨ p2))) ∧ True) ∧ (p4 ∧ p3))) → (True → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p1 → (((p3 ∨ p4) ∧ p4) ∧ p4)) → (p2 ∨ (False → False))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h3
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324888327023766500059336379610 : (p5 ∨ ((True ∧ p5) ∨ (p4 ∨ ((p4 ∨ (((True ∧ True) → (p4 ∧ (True → (p2 ∨ True)))) ∧ (p5 → p4))) ∨ ((False ∧ (p1 ∧ p3)) → p4))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610435800477734698881454760146 : ((((((((p2 ∨ True) ∨ (p2 → True)) ∨ (p3 ∧ ((p4 ∧ (p3 ∨ p1)) → (((p1 ∨ True) ∧ p3) ∧ (p1 ∧ False))))) → p1) → p5) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_119607186659660477558006230928 : ((p5 → (p2 ∨ (p4 ∨ ((p2 ∧ ((p4 ∧ False) ∧ p5)) ∧ (p4 → (((p3 → (((p5 ∨ p2) ∨ p2) ∧ p2)) → p3) ∧ p4)))))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55253213451703093621846904514 : ((((p3 ∧ p4) ∨ ((p3 → p4) → False)) ∨ (((p5 ∧ p3) → ((p2 ∨ (True ∧ p2)) ∨ (True ∨ ((p4 ∨ p2) ∧ p3)))) → (p3 → p3))) ∨ p3) := by
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
theorem thm_5_vars_116710151178753828163069094040 : (((p1 ∧ p3) ∨ (p4 ∨ ((p3 ∨ ((p1 ∨ True) ∨ ((((False → p2) ∨ (p5 ∧ p2)) → True) ∧ (True → True)))) ∨ (p5 ∧ p3)))) ∨ (p1 ∨ p1)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197394039757529501514358454462 : (((p4 ∨ (p3 → (False ∨ (p1 ∧ False)))) → p3) ∨ (False ∨ ((p2 → (p4 ∨ ((p1 ∧ p1) → (((False → p3) ∧ True) ∨ p3)))) ∨ (p3 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227984358232068347726000306563 : ((p3 ∧ (p2 ∨ p5)) ∨ ((p2 → (False ∨ False)) → ((((((True ∧ True) ∨ p4) ∧ (p3 ∨ (p4 → p4))) ∨ (True ∧ p1)) → p1) ∨ (p3 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179088772600826720097366184326 : ((False ∧ (((p5 → (p3 ∧ (p4 ∨ True))) → (p3 ∧ (True → False))) ∧ p1)) ∨ ((((p3 ∧ p1) ∨ (False → (p5 ∧ p5))) ∨ p4) ∧ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111761866538208727967228242154 : (((((True → (((((p3 ∨ ((p4 → (p1 ∨ p1)) ∧ p3)) ∨ p3) ∧ p2) ∧ p3) ∧ p2)) → (p5 ∧ p2)) ∧ (p2 ∧ p3)) ∨ p3) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345135849469975305214461784005 : (p3 → (((p2 ∧ (p1 → (p1 ∨ p4))) ∨ ((((p1 → True) → p1) → (((p4 ∨ p5) ∨ p1) ∨ (False → (p3 → p1)))) ∧ (p5 ∨ p3))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219052666500776513893971604464 : ((p5 ∧ (True ∧ (p5 ∧ True))) → (((p2 ∨ (p2 ∨ p2)) ∨ (p1 ∧ p1)) ∨ (((p3 ∨ p2) ∧ ((p1 ∧ True) ∧ p1)) ∨ ((p5 ∧ p1) ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323181470142945321799128880399 : (p5 ∨ ((((p1 → ((p1 ∨ (p4 ∧ (p3 ∨ True))) → p2)) → ((False ∧ (((p2 → p1) → (p3 ∧ p1)) ∧ p1)) ∨ True)) ∨ False) ∨ (p3 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249292162334051594476766953829 : ((p4 ∨ p5) ∨ (((p1 ∧ True) ∨ (((False ∨ ((p4 → ((p5 ∨ ((p1 ∨ False) ∨ False)) ∨ ((True ∨ p2) ∧ p2))) ∧ p4)) ∨ p3) ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114161302115116455494267832066 : (((((((((True ∧ p1) ∧ True) ∧ p2) ∨ p4) → (p2 ∧ (p2 ∧ p5))) ∧ ((p5 ∧ p2) ∨ False)) → p1) → (p3 → (True ∧ p1))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193887485210256283834190817108 : ((False ∨ ((p2 ∧ True) ∨ ((p5 → p2) → (p4 ∧ False)))) → ((p4 ∨ (False ∨ ((p3 ∨ p5) ∧ (True ∧ p3)))) ∨ (True ∨ ((True ∨ p3) ∧ p2)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257984209530221876399763479735 : ((p4 ∨ p1) → (((((True → (((p1 ∧ p2) ∧ p1) ∧ True)) → p4) ∨ (p4 ∧ (True ∨ ((True ∧ False) ∧ (p5 → p5))))) ∨ True) ∧ (True ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
theorem thm_5_vars_181209223611680809050733287914 : ((p2 ∧ (((p4 → p3) ∨ False) ∧ ((False ∧ (p5 ∨ (p4 ∧ p3))) → False))) → (False ∨ (((p3 ∧ p3) ∨ ((False → (True → p1)) → p2)) ∧ True))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h2
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_132843056953380477610583952205 : ((p2 ∨ (True → ((p3 ∨ p4) ∨ (((((True ∨ (p5 → False)) ∧ p3) ∨ True) ∨ (((p1 → False) → False) ∨ p4)) ∨ p3)))) ∧ ((p3 ∧ p1) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748839661137745056098032350467 : ((((p4 → False) → ((p5 ∨ p1) → ((False ∨ ((((True → p4) ∧ ((p4 ∧ ((True → p5) → p5)) ∨ True)) ∨ False) ∨ (True ∨ False))) ∨ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586230467111729139240529974979 : ((((((((p4 ∨ (p1 ∨ (p4 ∧ p4))) ∧ (False ∨ True)) → p1) ∧ ((p3 ∨ False) ∨ ((p5 ∨ False) ∧ ((p4 ∨ p3) ∨ p4)))) ∧ p5) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54674728350569561664856205017 : (((((p5 → (p1 ∧ (True ∨ True))) ∨ p3) → p2) → (((((p2 ∧ (p5 → (p4 ∨ p2))) → (p2 ∨ True)) ∨ (p2 ∧ p4)) ∧ p2) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_96396189990834847580273094049 : ((False ∨ (((((p4 ∨ True) → p1) ∧ ((p1 ∧ (p1 → p5)) ∧ p2)) ∧ (p5 → ((p1 ∨ (p4 → False)) ∨ p4))) ∧ ((p4 ∨ False) ∧ p1))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h5.left
    let h15 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h17 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h18 := h13 h17
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187113786956548639296419986067 : (((p3 ∧ p2) ∨ ((p5 ∨ (p5 → ((p1 → p5) ∧ p1))) ∧ p1)) → ((((p4 ∨ ((p1 ∧ (p4 ∨ p4)) → p4)) ∧ p2) ∨ p1) ∧ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40388917336016725459758659605 : (((((((((((p1 → (True → p2)) → p3) → (True → (True → False))) ∧ p5) → (False → p3)) ∧ True) ∧ True) → (p4 ∨ False)) ∨ p4) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790726961194034763775700504226 : (((p5 ∨ (True → ((False ∨ (p4 ∧ (((p1 ∧ p4) → (p3 → (False ∧ p5))) ∧ p4))) ∧ ((((p4 ∧ p5) → p3) → (p2 ∨ p1)) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677868242505188060422763866332 : ((((((((p2 → True) ∧ (p5 → (p3 ∧ (((p4 → p4) ∨ p1) ∧ p2)))) ∧ p5) ∨ p3) ∨ (p5 ∧ True)) ∨ ((False → p1) ∧ (p3 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698963297657158971075103492965 : ((((p5 ∧ ((False → (p5 → p4)) → ((p3 ∧ p5) ∧ (True → False)))) ∨ (True ∨ ((False ∨ (p2 ∧ (True ∨ (p3 ∨ (p1 ∨ p4))))) → p4))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_66521623758647997236748417386 : ((True → ((((p2 → (((((False ∧ (p4 ∧ p4)) ∨ (p5 → p2)) ∨ (p3 ∨ p5)) ∨ p4) ∧ p3)) → (True ∨ p3)) ∧ (p4 → False)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233818355450213263526251074050 : ((p3 ∨ (p4 → p2)) → (((True ∨ p3) ∧ (((((p1 ∧ p5) → (p4 → ((p2 ∧ p1) ∧ (p4 ∧ False)))) → (p3 ∨ p2)) ∧ p3) ∨ True)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179463177437269032716904593221 : ((p5 ∨ (p2 ∨ (p3 ∧ (((False → p5) → p3) ∧ ((True → p3) ∨ p5))))) ∨ ((((((False ∨ p2) ∨ p1) ∧ False) → p5) ∧ False) → (True → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723944187893086764313868329290 : ((((False ∧ (True ∧ p4)) ∧ ((p4 → (p5 ∨ (p3 ∧ (p4 → (p1 ∨ ((p4 ∧ False) ∨ p3)))))) ∨ (((p2 → p3) ∧ True) → (p1 ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300811081123537381965529179726 : (False ∨ ((((p3 → (((False ∧ p3) → p1) → (p5 ∨ p5))) ∨ (True ∨ True)) ∧ (p5 ∨ p4)) → (True ∧ ((((True ∧ p2) ∨ False) ∨ True) ∨ p3)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347424808531995176242597699708 : (p3 → ((p4 ∨ ((p5 ∨ ((p5 ∨ p3) ∨ p3)) → p4)) → ((((p2 ∧ ((False → p1) → p5)) → (p3 ∧ (p3 ∨ p5))) → (True → False)) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : ((p2 ∧ ((False → p1) → p5)) → (p3 ∧ (p3 ∨ p5))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h1
      -- Conjunctions on the left can always be decomposed.
      let h9 := h6.left
      let h10 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h5
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h15 : ((p2 ∧ ((False → p1) → p5)) → (p3 ∧ (p3 ∨ p5))) := by
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h1
      -- Conjunctions on the left can always be decomposed.
      let h19 := h16.left
      let h20 := h16.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h21 := h3 h15
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h22 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h23 := h21 h22
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68431971161455625681482898204 : ((p3 → ((True ∨ p3) → (p5 ∨ (((False ∨ p4) ∨ (True ∧ p3)) ∨ (p2 ∧ (((True ∧ True) ∧ (p5 ∨ True)) ∧ ((p1 → p3) ∧ p1))))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201214959108305712520116387806 : ((p2 → ((((True ∧ p1) ∧ p5) → False) → p1)) → (((p2 ∧ (p3 ∧ p1)) ∨ p1) ∨ (p3 ∨ ((p5 ∨ (p5 ∨ p5)) → ((p1 ∧ False) → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_351748878007656854537278805477 : (p4 → ((((p2 → (True ∨ p1)) ∨ ((False ∨ ((True ∨ p4) ∧ p1)) → p4)) ∧ p2) → (((p5 ∨ (p3 ∧ p4)) → ((p1 ∧ False) ∨ p1)) ∨ p4))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36201463302401332393891657539 : ((p4 → ((((((p1 ∨ True) ∧ True) ∧ False) ∨ (((p2 ∨ (p5 ∧ True)) ∨ (p5 ∧ (((p3 ∨ p1) → p5) ∧ p3))) ∧ False)) ∨ True) ∧ p4)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300075548504877999934403559188 : (False ∨ ((((((True → (p5 → p2)) ∨ (p2 ∧ p3)) ∨ (((p2 ∨ p1) ∨ p4) ∨ (p1 → p1))) ∧ (p4 ∧ (p5 ∧ True))) → p1) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719099185881010106134637242883 : ((((False ∧ ((p4 ∧ p5) → p2)) ∨ (((p4 ∨ p1) ∧ (p2 ∧ (p3 ∨ False))) ∨ ((False ∨ ((p2 ∧ (p1 → False)) ∨ (False ∧ p5))) → True))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_64869421572155182122679686388 : ((p2 ∨ ((p1 ∨ ((((p5 → (False ∨ ((False ∧ p1) → p1))) ∧ p3) ∧ (p1 → ((True ∧ p3) ∨ (p2 → p4)))) ∧ True)) ∨ (True ∨ p4))) ∨ p2) := by
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
theorem thm_5_vars_192660408007269871799188227383 : ((((((p1 → p2) ∨ (False → p5)) → p1) → p2) → p4) → (((p1 ∨ ((p5 ∨ (p5 ∧ p1)) → p1)) ∨ p5) ∨ ((p1 ∨ p3) ∨ (p3 → p3)))) := by
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
theorem thm_5_vars_829259062319823529627254390901 : ((((False ∨ ((False → p2) → ((((p2 ∧ ((p2 → p2) ∨ (p3 ∨ (p2 ∨ (p4 ∧ p3))))) ∧ p4) ∧ (p2 ∧ (False ∨ p5))) ∧ p4))) ∧ p4) → p5) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (False → p2) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h6
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660517156133395092808116618421 : ((((((p1 ∧ ((p3 ∨ ((p2 ∧ ((True ∧ p3) → (p1 ∧ p3))) ∧ False)) ∨ (p3 → ((True ∨ p4) → p2)))) ∨ p4) → p5) → (p4 → p5)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p1 ∧ ((p3 ∨ ((p2 ∧ ((True ∧ p3) → (p1 ∧ p3))) ∧ False)) ∨ (p3 → ((True ∨ p4) → p2)))) ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309638129046527851863763641752 : (p2 ∨ ((((p5 ∨ p1) ∨ p2) ∨ (p3 ∧ (False ∨ ((p5 → (True ∨ (((p1 ∧ p3) ∧ (p2 ∧ p4)) ∨ p4))) → p3)))) ∨ ((p3 → p3) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204120704576861858310783017897 : (((((p5 ∨ p1) → False) ∧ p3) ∧ False) ∨ ((((False ∨ False) ∧ False) ∧ ((p2 ∨ (p1 → (p1 → p3))) → ((True ∧ p5) ∧ p2))) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307364708882248505511874208043 : (p1 ∨ (p4 ∨ ((((p5 ∧ p5) → p1) → (((((p4 ∨ p1) ∨ ((p2 ∧ p3) → False)) → True) ∨ (p3 → (p1 → (p1 ∨ p2)))) → p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54174185689402416802934781781 : ((((((True → p1) ∧ False) ∨ (True → p2)) ∧ p5) ∧ ((((p2 → p2) ∨ p2) ∧ True) ∧ ((p2 ∧ ((p5 → p2) ∨ (p5 → True))) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300538072488313058464438682899 : (False ∨ ((((p2 ∧ p4) ∨ (p2 ∧ ((p1 ∧ (((p2 ∨ p2) ∧ p4) ∧ False)) ∧ ((True ∧ True) → p1)))) ∨ True) ∨ (((p1 ∨ p4) ∨ p1) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84100950666267118158171127673 : ((((p3 → (p4 → p2)) ∧ ((False ∨ (True → ((p4 → (p3 ∧ p4)) ∧ False))) ∨ False)) ∧ (p4 ∨ ((p5 ∧ (p2 ∨ False)) ∧ (p2 ∨ False)))) → p1) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h9 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h10 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h11 := h8 h10
        -- We need to get the right conjuct of h11 based on <expert-advice>.
        let h12 := h11.right
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Conjunctions on the left can always be decomposed.
        let h16 := h14.left
        let h17 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h19 =>
            -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
            have h20 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h8, we can now drive its conclusion.
            let h21 := h8 h20
            -- We need to get the right conjuct of h21 based on <expert-advice>.
            let h22 := h21.right
            -- False on the left can always be used.
            apply False.elim h22
          case inr h23 =>
            -- False on the left can always be used.
            apply False.elim h23
        case inr h24 =>
          -- False on the left can always be used.
          apply False.elim h24
  case inr h25 =>
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113687335932920679287295998272 : ((((((((True ∧ p5) ∨ (p1 → p1)) ∧ p5) ∧ ((((True ∧ True) ∧ p1) ∨ p2) → (p1 ∧ True))) → False) → p2) → (p2 → p1)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



