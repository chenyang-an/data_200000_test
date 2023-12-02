variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111660230457010390048808883738 : ((((p4 ∧ ((p5 → (p4 ∨ ((((False → p2) ∧ p5) ∧ (p3 → (True ∧ ((p3 → True) ∧ p4)))) → p2))) ∧ True)) ∨ False) ∨ p2) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147959133240738788593102346469 : (((False ∨ (((p2 ∧ False) ∧ ((p5 → (True → ((p5 ∧ p5) ∧ p1))) ∨ p3)) ∨ (p3 → True))) ∧ (p3 → p2)) ∨ ((p5 ∧ (True ∧ p4)) → p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27677092544360519134692351947 : (((p1 ∨ p4) → ((((p3 → (True ∨ (p5 ∧ (False ∨ (p1 → p2))))) → p1) ∨ True) ∨ ((True ∧ True) → (((p3 ∨ p3) ∧ p2) ∧ p3)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726497803548084630162313450216 : (((((p3 → p1) ∨ p5) ∨ (((p1 → ((((False ∨ (False ∨ (p1 ∨ (p4 ∧ (p4 ∨ (p5 ∧ p3)))))) ∧ p3) ∧ p3) ∨ True)) → p5) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_51480488631301501414263748176 : ((((((True ∨ p2) ∨ (p4 ∨ True)) ∨ p5) ∨ ((p2 ∨ (p4 → p1)) ∨ ((p5 ∨ p1) ∨ p2))) → (((False ∧ (True ∨ False)) → p5) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616109231470968801460823023116 : ((((((((p3 ∨ (p3 → (False → p3))) ∧ True) ∧ (p4 ∨ p2)) ∨ False) ∧ (p4 ∨ (((p2 ∧ (p4 ∧ True)) ∧ (p3 ∨ p3)) ∨ p2))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148120699864798173450566676600 : (((((False ∨ p2) ∨ (p1 ∧ p4)) ∨ ((p2 ∨ ((p4 ∧ p1) ∧ p5)) ∨ (p4 ∨ (p1 ∨ p3)))) → (False ∨ p5)) ∨ (((True ∨ p3) ∨ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149139330445494196696064193833 : (((p5 ∧ p1) ∧ ((p4 → (False ∧ ((((False ∧ p3) → p3) ∨ True) ∨ (p1 ∧ p2)))) ∧ ((p1 → p3) ∨ p5))) ∨ ((False ∧ p1) → (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164614978424307731400555935162 : (((p3 ∧ ((True → ((p2 → (False ∧ p1)) ∨ (False ∨ p4))) ∧ ((p4 ∨ p5) → p2))) ∧ p1) ∨ ((p2 ∧ (True ∨ (p2 → (p3 ∧ p5)))) → p2)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660095551499634441132949066115 : (((((((p1 → ((True ∧ (p4 ∨ (((p1 ∧ p5) ∨ False) ∧ p4))) ∨ False)) ∧ (p2 ∨ p3)) ∨ ((p1 ∧ p3) ∨ p1)) ∨ True) → (p4 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599539551742098703743022616426 : (((((p3 ∨ p1) ∨ ((((p4 ∧ (p3 ∨ (((p2 → ((p5 ∧ ((p2 → p4) ∨ p3)) ∧ p5)) ∨ False) → p3))) ∨ False) ∨ p3) ∨ p3)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234645093154540878546580162765 : ((p3 → (p4 → p2)) → ((p3 ∧ (p4 ∨ ((p2 ∧ False) ∨ ((((p5 ∧ True) ∧ True) ∧ (p5 ∨ (p3 ∧ p2))) ∨ (p5 → p4))))) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681356825504881726165500822105 : ((((p1 ∨ (((False → (((p1 → True) → p2) ∨ p4)) ∧ ((p1 ∨ p4) → (p2 ∧ (p4 → False)))) → True)) → (p5 ∨ ((p4 ∨ p3) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324021539952570832316480262788 : (p5 ∨ ((((p5 ∨ (p5 ∧ p4)) ∨ ((p1 ∧ p5) ∧ True)) ∨ ((True → p1) ∨ False)) → ((((True ∧ p1) ∧ False) ∨ True) ∨ ((p3 ∨ p2) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
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
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167696849968984954491654936647 : ((((p5 ∧ (p2 → (p3 ∧ p5))) ∧ (p2 ∨ (p2 ∧ (True → p2)))) ∧ (p1 ∨ (False ∧ p5))) → (((p3 ∧ True) → (p3 → False)) ∨ (p3 ∨ p1))) := by
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
  cases h5
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799418602605376888199090320470 : (((p1 → (False ∨ (((p1 ∨ (p3 → p4)) ∧ (p4 ∨ ((False → (p2 → p1)) → p5))) → (p1 → ((((p3 ∨ p3) ∨ p3) ∨ p2) ∨ p1))))) ∨ p4) ∧ True) := by
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
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807921502960498927241922165464 : (((p4 → ((p2 → p1) ∨ (p2 ∧ (((p2 ∨ (p3 ∧ (p4 → True))) ∨ ((p3 ∧ p3) ∧ (p1 → (p2 ∨ False)))) → ((False ∧ p1) ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40787591119326193140990975844 : ((((p3 ∧ ((p3 → ((p1 → p3) → (((p1 ∧ p2) ∧ p2) → True))) ∧ ((p2 ∧ (p4 → p2)) ∧ (p3 ∧ (p5 ∧ p3))))) → p4) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806160796133675922414941019197 : (((p4 → (((p3 ∨ (p3 ∧ ((((False ∧ p1) → p1) → (p4 → ((False ∧ True) ∧ (False ∨ (p4 ∨ (p4 ∨ p3)))))) ∨ False))) ∧ p3) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_156992103537587732274900281894 : ((((p1 ∧ ((p2 → (p5 ∨ p2)) ∧ p4)) → ((((False → False) → (False ∧ p3)) ∨ p4) ∧ p1)) ∨ p3) ∨ ((p5 → (p2 ∨ (p5 ∧ True))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228848735501608948968284708000 : ((p3 ∨ (p2 → p3)) ∨ ((False ∧ p1) ∨ (((p4 → (False ∨ (p3 → (((False ∧ ((p2 ∧ p4) ∨ p4)) ∧ p5) → (False ∨ p3))))) → False) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → (False ∨ (p3 → (((False ∧ ((p2 ∧ p4) ∨ p4)) ∧ p5) → (False ∨ p3))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692417806461875596913653093314 : (((((False → (((p4 ∨ (p2 ∧ (p5 → True))) → p5) ∨ (False ∧ False))) → p5) ∧ (((p2 ∨ (True ∧ p3)) ∨ (p4 ∧ True)) → (p4 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684081887068593105479775228043 : (((((p4 → (p3 ∨ (((False ∧ (True → (((p5 → False) ∧ False) ∧ p2))) ∨ p2) ∧ p1))) → False) ∨ (p4 ∨ ((p2 ∧ (True → False)) → p2))) ∨ p5) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258759219876675608660682760498 : ((True → False) → (((((((p3 ∨ False) → True) ∨ p1) ∨ (p2 ∧ (True ∨ p1))) ∨ p3) ∧ (p2 ∨ ((p3 ∨ (p3 ∨ p4)) ∨ (False → p1)))) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207037200006715997390276919057 : ((((p5 ∨ p2) → (p4 ∨ p5)) ∧ p4) → (((True ∨ False) ∧ ((((p2 ∨ (p4 → True)) ∨ p4) → ((p4 ∧ p5) ∧ False)) ∧ (p5 → True))) → p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h10 : ((p2 ∨ (p4 → True)) ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h11 := h6 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244899833552427771319111523048 : ((p1 ∧ p2) ∨ (False ∨ (((p2 ∧ (((p3 → p1) ∧ p2) ∨ p5)) ∨ (p1 ∨ ((((p4 ∧ p5) ∨ True) ∧ (True → (p2 ∧ p3))) → p2))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- One of the premise coincides with the conclusion.
    exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218331337466463598532593297919 : (((False → p3) ∨ (p2 ∧ True)) → (p4 → ((((((p5 → ((p5 ∨ (True ∨ (p4 ∧ True))) ∨ p2)) ∨ p1) → (True ∧ p2)) → p2) → False) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : ((((p5 → ((p5 ∨ (True ∨ (p4 ∧ True))) ∨ p2)) ∨ p1) → (True ∧ p2)) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : ((p5 → ((p5 ∨ (True ∨ (p4 ∧ True))) ∨ p2)) ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h8
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h9 := h6 h7
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h5
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158203071112664800295807428436 : ((((True ∨ p4) ∨ p4) ∧ (((p3 ∧ p4) ∧ (False → (p5 ∧ p1))) ∨ (p5 ∨ ((p5 ∨ p1) ∧ p3)))) ∨ (((p3 ∧ (p3 ∧ True)) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214574855101915036783321545386 : (((p2 ∨ p4) ∧ (p4 ∧ p5)) ∨ ((p4 ∧ True) ∨ ((p4 → ((((p4 ∨ p5) ∨ True) ∧ p5) ∨ p5)) ∨ (((False ∧ False) ∨ p5) → (True ∨ p2))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234092678859640210404715125529 : ((True → (p4 ∧ False)) → ((p4 ∧ p4) ∧ (((((p2 ∨ True) ∧ ((p2 ∨ p3) ∨ (p1 ∨ (True ∨ (p2 ∧ p1))))) ∧ p5) ∧ p5) ∨ (p1 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- One of the premise coincides with the conclusion.
  exact h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230704271802958931892822373358 : (((p4 → p3) ∧ p3) → ((p1 → (((p5 ∨ True) → p4) ∧ True)) ∨ ((True ∨ False) ∨ (((True ∨ (p3 ∧ ((p2 → False) → p4))) ∨ False) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192524055927089533788686904698 : ((((False → True) → ((True → (p1 ∨ p2)) → p5)) ∨ True) → (((p1 ∨ (True ∨ (p2 → True))) → p1) ∨ ((p3 ∧ (p3 ∨ True)) → (True ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146901880064262572850150255022 : ((((((((p4 → p2) ∨ p1) ∧ ((p4 → p1) ∧ ((p1 ∧ p1) → p1))) ∨ (False ∨ p2)) ∧ p1) ∧ p1) ∧ p5) ∨ ((p5 → True) ∨ (p4 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698711353942627357543107485624 : (((((p3 ∨ p5) ∧ ((p2 ∧ ((p4 ∨ p5) → (p5 → p4))) ∧ p2)) ∨ ((((p5 ∧ p4) ∨ p3) ∨ (p4 ∨ p4)) ∨ (False → (p3 → p4)))) ∨ p4) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184155582460013975094975125252 : (((p2 ∨ (p2 ∨ (p3 ∨ ((p4 ∧ p1) ∨ (p1 → True))))) ∨ True) ∨ ((p1 → ((p5 ∧ p2) ∧ (p5 ∧ False))) ∨ ((p3 ∧ p5) ∧ (p2 ∨ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706631252565250019864566030741 : ((((p3 → (((True ∧ (False → p2)) ∧ p2) → p1)) ∧ (p1 ∧ (p1 ∧ (False ∨ ((((p2 → (p1 ∧ p5)) ∨ True) ∨ p4) ∨ (True → p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2691442634831156370684692833 : (((p1 ∨ ((p4 ∨ True) ∨ p5)) → p5) → (((p5 ∧ False) → p1) → (((True ∧ (p4 ∨ p1)) → p1) ∨ ((p3 ∧ (p2 ∧ p5)) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179127553120283958851274443788 : ((p1 ∧ ((((p1 ∨ (p5 ∧ (p3 → False))) ∧ p1) ∨ p1) → (p3 ∧ p5))) ∨ (False ∨ ((p1 → p2) → (((p5 → False) → (p4 → p4)) → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156933979062665579210982771955 : (((((False → p1) → (((p5 ∧ (p5 → True)) → p4) ∧ ((p3 ∨ p2) → p2))) ∧ (p4 ∨ p1)) ∨ p3) ∨ ((p1 ∧ True) ∨ ((False ∨ p1) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204562137116154476801958254280 : ((((p1 ∧ p3) ∧ (p5 ∧ False)) ∨ False) ∨ (True → (((((True ∨ p4) ∨ True) → p1) ∧ True) → ((((False ∨ (True ∧ p1)) ∨ p4) ∧ p1) → p1)))) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h2.left
      let h12 := h2.right
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h2.left
    let h15 := h2.right
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675530943621301659036784031309 : ((((((True ∧ ((((True ∨ True) ∧ (p1 ∧ True)) ∨ (p1 ∧ p1)) ∧ p5)) ∨ (p3 → p5)) ∧ (p4 ∧ p1)) ∧ ((p5 ∧ True) → (False → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118599490650570482208220883554 : ((p4 ∨ ((p2 → (((p2 ∧ p1) ∨ p1) → (((p3 → (p3 ∧ p1)) ∨ p4) → (((p3 ∧ True) ∧ p3) ∧ p5)))) ∨ (False ∨ p1))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798345202627589878477856431820 : (((p1 → ((((p4 ∧ True) → ((p2 ∨ ((p5 → p3) ∨ False)) ∨ False)) ∧ (p4 ∨ p1)) → (p4 ∧ (p2 ∨ (True ∧ ((p4 → p5) ∨ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682336007524661724012114105259 : (((((((p3 ∧ True) ∨ p5) → (True → (p2 ∨ (p5 ∨ ((True ∨ p2) → p1))))) ∨ (p3 → p5)) ∧ (((p5 ∨ (p2 → p1)) ∨ p4) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597543963964634722810244825292 : (((((p5 ∨ ((p5 → False) → p2)) ∨ (((p3 → ((p3 ∧ False) → True)) → (p2 ∧ False)) ∧ ((((False → p5) → p3) ∧ False) ∧ True))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614782431089617650497182786962 : ((((((True ∧ (True → p4)) ∧ (((((p5 ∧ (p4 → p4)) ∨ p2) ∧ (p5 ∧ False)) ∨ False) ∧ True)) ∨ ((p3 → p3) ∧ (p2 → True))) ∨ p1) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_327942470634201302481292756932 : (True → ((((True ∧ (((p1 → ((((p1 → p4) ∨ p2) ∧ (p1 ∨ True)) → p5)) ∨ (True ∨ p2)) ∧ p4)) ∨ p2) ∨ (p5 → p5)) → (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h13 =>
          -- One of the premise coincides with the conclusion.
          exact h3
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h15 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342177617172463680647857945473 : (p2 → ((p1 ∨ ((p4 ∨ p2) ∧ ((p1 ∨ (p4 ∨ ((((False → p2) → p5) ∧ p3) ∨ (True ∧ True)))) ∧ False))) ∨ (((p1 ∨ p3) ∧ False) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50705754222100933735600535995 : ((((False ∨ True) ∧ (((p4 ∨ (((p4 ∧ ((p1 ∧ p1) ∨ (p3 → False))) ∨ False) → p2)) ∨ True) ∨ p4)) → (p1 → (p3 → (False ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76468224962415706026217635511 : (((((p4 ∨ ((((p4 → ((p2 ∨ p4) ∨ False)) → (p5 ∧ (p2 ∨ p2))) → True) → (p1 ∨ p3))) ∨ p5) ∨ (p4 → (p4 ∨ p3))) → p3) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∨ ((((p4 → ((p2 ∨ p4) ∨ False)) → (p5 ∧ (p2 ∨ p2))) → True) → (p1 ∨ p3))) ∨ p5) ∨ (p4 → (p4 ∨ p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180303176982089749808559877080 : (((((False ∧ (p3 ∨ p2)) ∧ (p2 → (p3 ∨ p1))) → False) ∧ (p2 ∨ p5)) → (((True → (p4 ∧ (p2 → p5))) ∧ p2) ∨ (True ∨ (p2 ∨ p3)))) := by
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
theorem thm_5_vars_46480432239698525716736085921 : (((((p2 ∧ p2) ∨ p2) ∨ ((p5 ∧ (False → False)) → (((((False ∧ (p1 ∨ p3)) ∧ False) ∨ p4) → p5) ∧ (p3 ∨ p1)))) ∧ (p5 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242353081494277080016740358364 : ((p2 → p2) ∧ (p4 ∨ (p5 ∨ ((((p5 ∧ p3) → (p2 ∧ (True ∨ p1))) → (p1 ∨ ((p1 ∨ p1) → p4))) ∨ (p3 → (True ∧ (p2 ∨ True))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65766785709507807087801478652 : ((p4 ∨ (((p2 → p3) ∧ (p5 ∧ ((False → ((False ∨ p2) ∧ False)) → ((p1 ∨ p1) → False)))) ∧ (p5 ∧ (p4 ∨ (p1 → (False ∨ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309299735194225352785780231711 : (p2 ∨ (((((True → ((True ∧ ((p4 ∨ (False ∧ ((p4 ∨ True) ∧ p1))) → p5)) ∧ False)) → p2) ∨ (p4 ∧ (p2 → p4))) ∧ True) ∨ (False ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345722083281574432533186899054 : (p3 → ((p3 → ((True ∨ ((p2 ∧ (p2 → p1)) → (p2 ∧ (((p5 ∧ p4) → ((p1 ∧ p5) ∧ p3)) → p4)))) → (p2 ∧ (p1 ∧ p3)))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61184371916958732135009422582 : ((False ∧ ((p2 ∨ True) ∧ (True → (False ∨ (((True ∧ p1) ∨ (((False → ((p2 → False) ∧ p4)) → ((p1 → False) ∨ p3)) ∨ p4)) ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743482585212468760899637622771 : ((((p5 → p4) ∨ (((p3 ∨ p2) ∧ p5) ∨ ((((((((p1 ∨ p3) ∨ True) ∨ p2) ∧ p4) ∨ (p3 ∨ True)) → False) ∧ p5) ∨ (True ∨ p1)))) ∨ False) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177735684405936847158750030223 : ((((p3 ∧ (p2 → p4)) ∧ ((p4 ∨ True) → (p4 ∧ (p4 → p3)))) ∧ True) ∨ ((p5 → p1) → (p4 → (True → (False → ((p1 → p5) ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763441689200939295579576464032 : (((p3 ∧ (False ∧ ((p1 ∨ p4) ∨ ((p5 ∨ (p3 ∧ p1)) ∧ (p1 ∨ (False ∨ ((p4 ∧ (((p5 ∧ p5) ∧ (p5 ∧ False)) ∧ p1)) → p2))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746259102149155922732014683479 : ((((p1 ∨ p5) → ((((True ∨ True) → p4) ∨ (((False → (p3 ∨ p5)) ∧ (True ∧ (p1 → False))) ∨ ((p1 ∧ p2) ∨ (p3 ∨ p5)))) ∨ p1)) ∨ p2) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
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
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43634224523676591508970417962 : ((((((p5 ∨ (((p2 → ((p5 → (p1 → ((p1 ∨ p5) ∧ False))) → p1)) → p4) ∨ (p4 ∧ p4))) ∨ False) ∨ (True ∨ p1)) → p5) → p5) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ (((p2 → ((p5 → (p1 → ((p1 ∨ p5) ∧ False))) → p1)) → p4) ∨ (p4 ∧ p4))) ∨ False) ∨ (True ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65119324147378727995854665896 : ((p2 ∨ (True → ((((p5 ∨ p2) ∨ (p2 → ((p3 ∧ (p1 → p4)) ∧ (p5 ∧ p4)))) ∧ p5) ∨ ((p5 ∨ (True ∨ (False → p4))) ∨ True)))) ∨ False) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768814011141864145176104068935 : (((p5 ∧ ((p3 ∧ (p4 → (p3 → (p2 ∨ p4)))) ∧ ((p3 ∧ (((((p4 ∨ (p3 ∧ p5)) ∧ True) → True) ∧ p2) ∧ (p2 ∨ p5))) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47085943639756031542922354571 : ((((((p1 ∧ ((p5 → True) ∨ p3)) → (True ∨ p1)) → (p2 ∧ ((p2 → (p1 ∧ False)) ∧ (False ∧ p5)))) → (p4 ∨ p3)) ∨ (True → p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∧ ((p5 → True) ∨ p3)) → (True ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43976436861546305112851193073 : ((((p4 → ((p4 ∨ (((True ∨ (p4 → (p2 ∨ (True ∨ ((p1 ∨ p4) ∧ (p2 → p4)))))) ∧ False) ∨ p2)) ∨ p2)) ∨ (p5 ∧ False)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329315666801182799272944663332 : (True → ((p2 → (p3 ∧ p2)) ∨ ((((p3 → (p3 ∧ (p5 → p5))) ∧ (False ∧ ((p1 ∧ (p1 ∧ False)) ∧ p5))) ∨ (True ∨ p2)) ∧ (False → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134132964818196640068467147204 : ((((((((p3 ∨ p2) → p4) ∨ (p2 → (False → ((p5 ∨ p4) ∧ p2)))) ∨ p2) → (p1 ∨ False)) → (p3 ∨ False)) ∨ p1) ∨ (False → (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158666071262166826807911073500 : ((p2 ∧ ((((True ∨ (p5 ∧ p3)) ∧ (True ∨ ((True ∧ ((False → p2) ∨ True)) ∧ p4))) ∧ p3) ∧ p5)) ∨ ((p2 ∧ False) ∨ (False → (p2 → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217110773617843490777174552032 : ((((False ∨ p2) ∨ p4) ∨ p2) → ((p3 ∧ (False ∧ (p5 → p3))) ∨ (p1 → ((p5 → (False ∨ (p5 → (p4 ∨ (p2 ∨ (p4 ∧ p2)))))) ∨ p3)))) := by
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
        -- False on the left can always be used.
        apply False.elim h4
      case inr h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h6
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h15
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184955753532007608105444753603 : ((((False ∧ True) → p4) → (((p1 → p2) ∧ (p4 ∨ p1)) ∧ p3)) ∨ ((p5 → (True ∨ True)) ∨ ((((p3 → (p2 → False)) ∧ p4) ∧ p2) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137417754142090348814322292795 : ((p4 ∧ ((((((p5 → p3) ∨ (((p2 → (False → (p4 → (True → p3)))) ∨ p1) ∨ p5)) → False) ∧ p1) ∧ p3) ∨ p3)) ∨ (p1 ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115268343882965073604952414397 : (((p2 ∧ (((p1 ∧ ((p2 ∨ False) → p4)) → p4) ∧ p3)) ∨ ((p4 → ((p2 ∧ (p2 ∨ True)) ∨ True)) ∨ ((p2 ∨ p2) ∧ False))) ∨ (p5 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_259009518402033638233236310873 : ((True → p4) → ((p3 ∧ (((False ∨ ((p4 ∨ ((p2 ∨ p3) → (p5 ∧ p5))) ∨ True)) → ((p3 ∨ (p1 → p2)) → p5)) ∨ (p1 ∨ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228568622999295453436654714382 : ((p1 ∨ (p1 ∨ p4)) ∨ (p3 → ((p5 ∨ (p3 ∧ (p4 ∨ p3))) → ((p3 → True) → ((p1 ∨ (((True → p5) → p1) ∨ (p2 → True))) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160230558668318806495495216675 : (((((p4 → p4) → ((p3 ∧ p1) ∨ ((p5 ∧ True) ∧ p3))) ∨ ((p5 ∨ p1) → p3)) ∨ (p2 → p3)) → (p5 → ((p3 ∨ p2) ∨ (False → True)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
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
theorem thm_5_vars_168826256572190252321239912316 : ((p3 ∨ ((((p1 ∧ False) ∧ (((p1 ∧ ((False ∨ p1) ∨ False)) → p4) ∨ False)) → True) ∧ p3)) → ((p5 ∧ ((p2 ∨ p2) ∧ (p5 → False))) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h9 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h10 := h6 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h14 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h15 := h6 h14
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h17 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h18 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h19 := h6 h18
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h23 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h24 := h6 h23
      -- False on the left can always be used.
      apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118263006478329871849645298941 : ((p1 ∨ (((((p1 → ((p5 → p4) ∧ (p1 ∨ True))) ∨ True) → p5) → p4) → ((p4 ∨ p3) → (p5 ∨ (p1 ∧ (False ∧ p5)))))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118550219268740322260537948053 : ((p3 ∨ (True → (((p2 → (p4 ∨ True)) → p3) ∨ (((p4 ∧ (p3 ∨ ((False ∧ False) → (p4 ∨ p5)))) ∨ p3) ∨ (False ∨ True))))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227281059889666759777110023892 : (((p1 → p3) → p5) ∨ ((((p5 ∨ True) ∧ ((((p2 → False) ∧ p5) ∧ (p1 ∧ (p4 → (p2 ∨ True)))) → True)) → (p3 ∨ (True ∨ p3))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_615058835629664237996026318413 : (((((p2 ∨ ((False ∨ ((p2 ∨ p2) → (p1 ∨ (p1 ∨ (True → ((p4 ∧ p5) ∧ True)))))) ∨ p3)) → (p5 → ((p5 ∨ p5) → p1))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_107607233213228920202672755480 : (((True ∨ p4) ∧ (((False → (p1 → ((((p1 ∧ (p4 → True)) → p4) ∧ True) → (p4 → p4)))) → (p5 → False)) ∨ (p1 ∨ True))) ∧ (p1 → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601942342647563801390481996224 : ((((p4 ∧ (p2 ∨ ((((p4 ∨ (p2 ∧ p2)) ∧ (p5 → p3)) ∨ ((p4 → p5) ∧ (True ∧ (((p2 ∨ p5) → p4) ∨ p2)))) ∨ p5))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782860132379569029896558311542 : (((p3 ∨ ((True → ((False ∧ p5) → (((p5 ∨ (((p4 → p5) ∧ p3) ∨ (p1 ∧ p3))) ∧ p2) → (p3 ∨ ((p2 ∧ True) ∧ p2))))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115498127534011088471928783915 : (((((((False ∧ p5) ∧ p2) → p4) ∨ False) → p4) → ((((p5 ∧ (p1 ∧ p4)) ∨ p4) → ((False ∨ p1) ∨ (p2 ∧ p4))) → p2)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225841796983615069548301098265 : (((False ∧ True) ∨ p5) ∨ ((((p2 ∧ False) ∨ (p3 ∧ (p3 ∧ ((p1 ∧ p4) → p4)))) ∨ (p1 ∧ p4)) ∨ (((p4 ∧ True) ∨ p3) → (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228707074636625522065206725625 : ((p2 ∨ (p5 ∨ p2)) ∨ (((((p4 ∨ False) → p4) ∨ p3) ∧ ((p5 ∨ p5) ∨ (p2 ∧ (((p4 ∨ False) ∧ (p4 → p2)) ∨ p4)))) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115974010823594385813607391891 : ((((False → (p3 → True)) ∧ p4) → (((False ∨ p1) ∨ (((False ∨ (True ∨ p4)) → ((p2 → p2) ∧ p4)) → (p4 ∨ True))) → p5)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48016077954755060946778030825 : ((((False → (((p1 ∧ False) ∨ (p3 → False)) ∧ ((p2 → p5) ∨ p1))) ∧ (p1 → (((p2 → (p1 ∨ p4)) ∨ p1) ∨ p1))) → (p3 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157779301397384415476167306650 : (((((p1 → (p1 → p4)) ∧ (p1 → ((p4 ∧ p3) ∧ True))) → p2) ∨ (False ∨ (p3 ∨ (True → p2)))) ∨ ((p1 → ((p2 → p4) ∧ False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346343479176946882103373225759 : (p3 → (((((p4 ∨ (False → p5)) → True) → p4) ∧ ((False ∨ (((p1 ∧ p5) ∨ ((p2 ∧ (False → p5)) ∧ p3)) ∧ p1)) ∨ p1)) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145109480707851941240611488959 : ((((p5 ∨ (p2 ∧ ((True → (p1 ∨ p1)) ∨ p1))) ∨ True) ∨ (p1 ∧ ((False ∨ p5) → (p2 → (p4 ∧ p3))))) ∧ ((p3 ∧ p2) → (p4 → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138335076942699112565281162016 : ((p3 → (p3 → ((False ∧ ((p3 ∨ True) → (p3 ∨ (p3 ∨ False)))) ∨ (p3 ∧ (p1 ∧ (p3 ∨ (p5 ∧ (p2 ∨ False)))))))) ∨ ((False → True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630194691373236139896499510638 : ((((((p5 ∨ p4) ∨ (p3 ∨ (((p3 ∧ (((p5 ∧ p1) ∧ (p3 ∧ p3)) → p5)) → (p4 ∧ p3)) → (p3 ∨ (p4 ∧ p3))))) ∨ False) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667238591938813632211175777509 : (((((p1 ∨ p5) ∧ ((p5 → p2) ∨ (p5 → (((((p3 ∧ (True ∧ p5)) ∨ p5) ∧ p3) ∨ p4) → (p1 ∨ p3))))) ∧ (True → (p4 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42199293900716022947296166513 : (((True ∧ (True ∧ ((((p1 ∨ (p3 ∨ True)) ∧ ((p3 ∧ (p5 ∧ (True ∨ p5))) ∧ False)) → (((True ∨ False) ∨ p3) → p1)) → False))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48166259012869295571561591387 : ((((p1 ∨ p4) ∧ (((p3 → p1) ∧ (((p5 ∨ p5) → True) ∧ (((False ∨ p2) → True) ∨ (True ∨ p5)))) ∨ (p2 ∧ p1))) → (p2 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260574574216611549018032398301 : ((p3 → p1) → (p1 → ((((p3 ∨ (p3 ∨ ((p3 ∨ (p2 ∧ (True ∨ (p2 ∨ (True → (True → p2)))))) ∧ False))) ∧ p4) ∧ (p1 → p5)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_922705036853727662804229653861 : ((((p2 ∨ ((((True ∧ (True ∧ (False ∧ True))) ∧ p4) → p4) ∨ (True ∨ p1))) → ((False → (((False → p4) ∨ (p4 → p1)) ∧ False)) ∧ False)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ ((((True ∧ (True ∧ (False ∧ True))) ∧ p4) → p4) ∨ (True ∨ p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214829337546488558308842796328 : (((p4 ∨ p4) ∨ (p4 → False)) ∨ ((((p5 ∨ (((False → p1) ∧ (True → p5)) → (p4 → (p3 ∧ False)))) ∧ (p1 → True)) ∧ p1) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



