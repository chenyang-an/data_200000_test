variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179018940093019068352904989319 : (((True ∨ p5) → (p1 ∨ ((p2 ∨ True) ∧ (p3 → ((p5 ∨ True) ∨ False))))) ∨ (((False ∧ p5) → (p5 ∧ (p5 ∨ p4))) ∨ ((p2 → False) → False))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136781461327051065038903098062 : (((True → p5) ∧ ((p4 ∧ (p2 ∧ (False ∧ True))) ∧ ((False ∧ p5) ∨ (((p2 ∧ p3) → p3) → (p5 → (p3 ∧ p1)))))) ∨ ((p3 ∧ False) → p2)) := by
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
theorem thm_5_vars_50365317337638633572281404693 : (((((False → p3) ∧ p1) ∨ (p4 ∨ (True ∧ (((p4 → False) ∧ ((p1 ∧ True) ∨ (True ∨ p3))) ∧ p4)))) ∨ ((p3 → False) ∨ (p2 → True))) ∨ p5) := by
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
theorem thm_5_vars_41607483817906257095717505069 : (((((p2 ∨ p3) ∧ ((p1 ∧ False) → (p1 ∨ p2))) ∨ (((False ∨ ((p2 ∨ (p2 ∧ p2)) → p4)) ∨ (p5 ∨ (p4 ∧ False))) ∨ True)) ∨ p4) ∨ p2) := by
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
theorem thm_5_vars_40142919976372659762720601045 : ((((((p3 → (p2 → (((p1 ∧ (False ∨ p4)) ∨ p5) ∧ p5))) ∧ (p3 ∧ p1)) ∧ (p5 ∨ ((p3 ∧ (True → True)) ∧ p4))) ∧ p2) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340958522105444971260528576444 : (p2 → ((((p2 ∧ p3) → True) → (((p4 ∨ p1) ∨ (True ∨ p5)) → ((((True ∧ p2) → (p2 → ((p2 ∨ p3) → True))) ∧ False) ∧ p4))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172159209486238513173263052357 : (((((False ∨ (True → (p1 ∧ (p5 → p1)))) ∨ p3) → p3) ∨ ((True ∧ p3) → False)) ∨ (False → (((((p2 ∧ p5) → p5) ∨ True) ∨ p1) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117530561595534711400445149063 : ((p2 ∧ ((p5 → ((True ∨ (p2 → ((p4 → (p2 ∨ False)) ∨ p2))) ∨ ((p2 ∧ ((True → p5) → (p1 ∨ p4))) ∨ p2))) → p1)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148006784610118681585419273612 : (((((False ∨ p4) ∧ ((False ∧ ((p5 ∨ p1) ∧ ((p3 → p3) → False))) → p2)) ∨ (p3 ∨ p4)) ∨ (p5 → p3)) ∨ (True → ((p1 → p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319681936043208256807283780245 : (p4 ∨ ((p2 ∧ ((p2 ∧ (p3 ∨ False)) ∨ (False ∧ False))) → ((p3 ∧ (p3 → ((((p3 → p3) → (p1 ∨ p4)) ∧ p4) ∨ p1))) ∨ (p2 ∨ p4)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218012367528085622383300947740 : (((True ∨ p3) ∧ (p3 ∨ p4)) → ((False ∨ ((p5 ∨ (p2 → p3)) → (p5 ∨ (p2 ∨ p2)))) ∨ ((False ∧ p2) → (False → (p4 ∨ (p5 ∨ p5)))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Implications on the right can always be decomposed.
      intro h17
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58102920526525042546617983870 : (((p1 ∧ p3) ∧ ((p4 ∨ ((((True ∧ ((False ∨ (False ∧ p4)) → (((p4 ∧ p5) → False) → p4))) ∧ (False ∧ p1)) → False) ∧ True)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766021140482210638563303215863 : (((p4 ∧ ((p1 ∨ (p3 → p4)) ∧ (((p1 ∧ p2) ∨ (((False ∨ (p3 → ((p3 ∨ ((False ∨ p1) ∨ p1)) → p2))) ∧ True) ∨ p5)) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144986520178861578981938181263 : ((((((p2 ∧ (True ∧ p4)) ∧ p3) ∧ p3) ∨ (p1 → (True ∨ p2))) ∧ (False ∨ ((p4 ∨ False) → (p1 → True)))) ∧ ((p3 ∧ p2) ∨ (False → p3))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310506101348071290953219014459 : (p2 ∨ (((p3 → p3) → (True → (p1 ∧ p2))) ∨ (((False → (((p3 ∧ False) ∨ p5) → p2)) ∨ (((False ∨ p3) ∨ (p3 ∧ p5)) → True)) ∨ p1))) := by
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
theorem thm_5_vars_339492578502641212545311511778 : (p1 → (False ∨ ((((p3 ∨ (((p2 ∧ (((((p4 → p3) ∨ p1) → p4) ∧ p3) → False)) ∨ p2) ∧ (p5 ∨ False))) → p3) ∨ p1) ∨ (p2 ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134825895926020450105728668564 : (((p1 ∨ (((True ∨ (((p1 → (p1 ∨ p1)) ∨ p5) → ((p3 → p2) ∧ (p4 ∨ False)))) → p4) ∨ (False → p1))) → p3) ∨ ((p4 ∨ p4) → p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39103846881587243277099660859 : ((((p2 → False) ∨ ((p4 ∧ ((p4 → (p3 ∧ p1)) ∨ (((True ∨ (p5 ∧ (p4 → True))) → ((p3 ∧ True) ∨ p5)) ∧ True))) ∨ p3)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185297975168573036002377949067 : ((p2 ∧ (p3 ∧ ((p4 ∨ ((p2 → (p4 ∨ True)) → True)) → False))) ∨ ((((((True ∨ p4) ∧ (p2 ∨ True)) ∧ False) ∧ p5) ∧ (p4 ∨ p5)) → p3)) := by
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
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180184952304217572642156873015 : ((((p2 ∧ (False ∧ (p1 ∨ p4))) ∨ (p1 ∨ (True ∨ (p2 ∨ p1)))) → False) → (((p1 ∨ ((p2 ∨ p3) ∧ False)) ∧ p5) ∧ (True ∧ (p2 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∧ (False ∧ (p1 ∨ p4))) ∨ (p1 ∨ (True ∨ (p2 ∨ p1)))) := by
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
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((p2 ∧ (False ∧ (p1 ∨ p4))) ∨ (p1 ∨ (True ∨ (p2 ∨ p1)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((p2 ∧ (False ∧ (p1 ∨ p4))) ∨ (p1 ∨ (True ∨ (p2 ∨ p1)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : ((p2 ∧ (False ∧ (p1 ∨ p4))) ∨ (p1 ∨ (True ∨ (p2 ∨ p1)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50187099361231750208948807232 : (((((p3 → (p3 ∨ p5)) ∧ ((p3 ∧ ((p5 ∧ (p3 → p5)) ∧ (False → False))) → (True → p4))) ∧ p1) ∨ (p3 ∨ (p1 ∨ (True ∨ p1)))) ∨ p4) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699623940504015415885083419402 : ((((((((p2 → p1) → p5) → p3) ∧ ((False → p3) ∨ p3)) → p3) → (((True → ((True → p5) ∧ (p5 → False))) ∧ True) ∧ (p2 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227412370753414040896607727200 : (((p5 → True) → False) ∨ ((p1 → (p5 → (p3 ∨ True))) → (p4 → ((p2 ∧ p1) ∨ ((p5 ∧ False) ∨ (((p1 ∨ (False → False)) ∨ p4) ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118165510821053466963130761699 : ((False ∨ ((p4 ∨ p1) ∧ ((p2 → ((True ∨ p2) ∧ True)) → ((p4 ∧ ((p4 ∨ ((p4 → (p3 ∨ p1)) ∨ True)) ∧ p2)) ∧ False)))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691753704795616305106796707070 : ((((p2 ∨ (((p5 ∨ (p2 → p1)) → ((p1 → False) ∧ p3)) → ((p4 → True) ∨ p4))) → (((p2 → False) ∧ (p2 → (True → p3))) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_111829091122731437403388488297 : ((((p4 ∧ (((p1 ∧ (False ∨ ((p4 → True) ∧ p5))) → p3) ∨ ((p2 → (False ∨ False)) → False))) ∧ ((p1 ∧ p4) → p4)) ∨ True) ∨ (True ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149623276675735228097854355880 : ((p3 ∧ (p3 → (((p2 ∨ ((False → ((p3 ∨ p1) → (p3 ∧ (True → True)))) ∧ p5)) ∧ (True → True)) → p2))) ∨ ((p1 → False) ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213421261752845788140852941569 : (((p3 ∨ (False ∧ p4)) ∧ p2) ∨ (p1 → ((p2 ∨ (p4 → ((p2 ∨ p3) ∧ False))) ∨ (((p4 → False) ∨ (p1 → (True ∧ (p2 ∧ False)))) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_164607645592920875855243410771 : (((p1 ∧ ((((p2 ∧ (p4 ∨ p5)) ∨ ((p5 ∨ (p3 ∨ p3)) ∨ p1)) ∧ p5) ∨ p3)) ∧ False) ∨ (True ∨ ((True ∨ False) ∨ ((p2 ∧ True) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174029262233316090562050881002 : (((p1 ∨ ((((p5 → (p1 ∨ (p4 → p4))) ∨ (False ∧ p1)) ∧ False) → False)) → p5) → (p3 ∨ ((p5 ∧ (True ∨ (p3 ∧ False))) ∨ (True → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ ((((p5 → (p1 ∨ (p4 → p4))) ∨ (False ∧ p1)) ∧ False) → False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h10
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148382586838562920965935524869 : (((((True ∨ (p5 ∧ True)) ∧ (p2 ∨ p5)) ∧ (p5 ∨ (p3 ∧ (p4 ∨ False)))) ∨ (True → (False ∧ (False ∨ False)))) ∨ (True → (True ∨ (p4 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48763426631638516496462068165 : ((((p4 ∧ p2) ∨ (p3 ∧ (p5 ∨ ((((p2 ∧ ((p1 ∧ (False → p3)) → p1)) ∨ (p4 ∧ True)) ∧ p2) ∨ False)))) ∧ (p1 ∧ (p1 ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313255959678986578854030374447 : (p3 ∨ (((p3 → p2) → ((((False ∨ p1) → (p1 ∨ (((p1 → p1) ∧ p1) ∨ (p3 ∨ p4)))) ∧ p4) ∧ (p2 ∧ (False → (p5 ∨ p2))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661499939461257269834265599249 : (((((p1 ∨ (False ∨ (False ∨ (((p3 ∧ (p2 ∨ (p5 ∨ p2))) ∧ p1) → (p3 → (p2 ∨ False)))))) ∧ (False ∨ (p1 ∨ p1))) → (True ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615070342415947424051578038765 : (((((True → (((p3 ∧ (p2 ∨ ((p3 ∨ p3) ∧ (p3 → ((p5 → p4) ∧ p2))))) ∧ True) ∧ False)) → ((False ∧ p3) ∨ (p3 ∧ p2))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348239063376674193769197843289 : (p3 → (True ∧ ((p2 ∨ (False ∨ (((p3 → True) → ((p3 → (p5 ∧ (p2 → (True → p2)))) ∧ (p4 ∨ (True ∧ (True → False))))) → p4))) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- False on the left can always be used.
    apply False.elim h12
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117845649081622517120954363093 : ((p4 ∧ (p2 → ((p5 ∧ ((p2 ∧ ((p5 ∧ (False → p2)) ∨ p4)) ∨ ((p4 ∨ ((p4 ∨ p1) ∧ p4)) ∧ (True ∧ p5)))) ∧ p4))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345331665523824934742616784624 : (p3 → ((((True ∨ ((True → ((p2 ∨ (False ∧ p1)) ∧ False)) → False)) → ((p4 ∨ ((False → (p3 → p3)) ∧ p5)) ∧ (p1 ∨ p3))) ∧ p3) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164441418859338222134532013175 : (((((((p5 ∨ ((False → p5) ∧ True)) ∧ (False → False)) → (p3 ∨ p1)) ∧ p1) ∧ p5) ∧ False) ∨ ((p3 ∨ p2) → (False → ((p1 → p5) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57078406487825741105034776080 : ((((False ∧ True) ∧ p3) ∨ (((p3 ∨ ((((p4 ∧ (p5 ∨ (p1 ∧ (p2 → False)))) ∧ p1) → True) ∨ p3)) ∨ p4) → ((p4 ∧ p1) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44950814455967462661306907170 : ((((p1 ∨ p3) ∧ (p4 → ((p4 ∧ (((p3 → (p1 ∨ p5)) ∧ (((p3 ∨ p5) ∨ p1) → p4)) → (p3 ∧ (False → p1)))) ∨ p5))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683513997755376133241437834194 : ((((p4 → (((p5 → p5) ∧ (((False → (p5 ∨ p4)) ∨ p3) ∨ p1)) ∧ (False ∨ (False → p3)))) ∧ ((False ∧ ((p1 ∨ True) ∧ p1)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350064242217654024273692700219 : (p4 → (((((True ∨ (p3 ∨ (False ∧ (p2 → ((p3 ∨ p4) ∧ False))))) → ((p5 ∧ p2) ∨ (p4 → (p3 → False)))) ∧ False) ∨ (p2 ∧ True)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88756801006588111459432482402 : ((((False ∧ (p4 → p1)) → False) → (((p5 ∨ (True ∨ True)) ∨ ((False ∧ ((False ∨ (p5 ∧ ((p4 → p1) → p3))) ∨ True)) → p3)) ∧ p2)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ (p4 → p1)) → False) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145900750105614174388911101733 : (((p1 → p4) → ((((p5 ∧ p3) ∧ p3) ∧ (((p5 ∧ (p2 → p1)) ∧ True) ∧ (p5 → (p3 ∧ p4)))) ∨ True)) ∧ ((True ∨ p5) ∨ (p5 → p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659165525275395975033074415790 : ((((p3 → ((p2 ∨ (False ∨ p1)) → ((p4 ∨ (p1 ∧ p5)) ∧ (True ∧ (((p1 ∧ True) ∨ (p4 ∨ False)) ∧ (False → p1)))))) ∨ (True ∨ p4)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_157727997808949881035879493174 : (((p5 ∧ ((((False → True) ∨ True) ∨ False) ∧ ((p1 ∧ p5) → (p1 ∨ False)))) → (p2 ∧ (p4 ∨ p5))) ∨ ((p2 ∨ ((p2 → p2) ∨ p1)) ∨ p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328276686183185702682545725928 : (True → (((False ∧ ((p2 → True) ∧ (p3 ∧ ((((p5 ∧ (p1 → p5)) ∧ (True → p1)) ∧ False) ∧ False)))) ∨ True) ∨ (((True → p3) ∧ False) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218339225017141545856647215464 : (((p1 → p1) ∨ (p2 ∧ p1)) → ((p1 → (False ∧ (p3 → (((p1 ∧ True) ∧ True) ∧ (p3 → ((p2 → p1) → p3)))))) ∨ (p5 ∨ (True ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
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
theorem thm_5_vars_174905551815751046186654673370 : (((True ∨ False) → (p5 ∨ (((True ∧ ((p5 ∨ (False ∨ p4)) ∨ p1)) ∧ p3) ∨ p4))) → (((((False ∨ p3) ∧ (p4 ∧ True)) → p5) ∧ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307272099866208262971930071866 : (p1 ∨ (p2 ∨ ((p2 ∨ (p3 ∨ False)) ∨ (p4 → (((True ∨ p5) → (False ∨ p1)) → ((True ∧ (p1 ∧ ((p1 ∨ (False → p3)) ∨ p1))) ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263170304121496816053447788367 : (True ∧ ((p4 ∨ (p2 ∨ ((((False → (p5 ∧ False)) ∨ ((True ∨ False) → p3)) → p2) ∨ (p3 ∨ (p1 ∨ ((p5 → p3) → True)))))) ∨ (p1 ∧ p2))) := by
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
theorem thm_5_vars_179172207044658219751595069127 : ((p2 ∧ (True → (((p1 ∨ (p2 → p3)) ∨ (False ∨ p3)) → (p4 ∨ p3)))) ∨ ((p1 → ((((p5 → True) ∨ (p5 ∨ p3)) → False) ∨ p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643892657429212477998745933137 : ((((p5 ∧ (True → (((((p3 → True) ∨ p3) ∨ ((p5 ∧ (((p3 → ((p2 ∧ p5) → p5)) → p2) → True)) ∨ p3)) ∨ p1) ∧ True))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695101447886987440367546334185 : (((((((p5 ∨ p2) → ((p2 ∧ (p1 ∧ False)) → (p3 → p1))) ∨ p4) ∨ p5) → ((True ∧ (((p2 ∧ p2) ∨ (p4 ∨ False)) ∨ p1)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171929576356625072450588116080 : ((((((p1 ∨ (p1 ∨ (p1 ∨ (p1 ∧ p4)))) ∧ p2) ∨ False) ∨ p4) ∧ (p5 ∧ True)) ∨ (((False → p5) ∧ p1) ∨ (((p4 ∧ p3) → p4) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259815746468657894399716499728 : ((p1 → p3) → (((((p2 ∧ (True ∨ p4)) ∧ ((((False → True) → p1) ∨ p5) ∨ p5)) ∧ p2) ∨ p2) ∨ (p2 ∨ (((p4 → p2) ∧ False) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304733205974244756756809601245 : (p1 ∨ ((((p4 → (True ∧ ((False → p2) ∧ p4))) → p5) ∧ ((False ∧ p4) → ((p5 ∨ (p2 ∨ ((True ∧ p3) → p2))) → p2))) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674597818425344695520919330645 : ((((False → (((((p2 → ((p5 → ((False ∨ p1) ∧ p4)) ∨ p5)) ∨ p5) ∧ ((p5 ∨ p3) ∨ True)) ∧ p2) ∨ False)) → ((p2 ∧ p5) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54095236517518018286769554644 : ((((p1 → True) → (((p1 ∧ (p2 → p1)) ∧ False) ∧ p2)) → (((p4 ∨ (False ∨ p5)) ∨ (p1 → (True → (p3 ∨ p3)))) ∧ (p5 → False))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (p1 → True) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h8
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113661390589424433653753218755 : (((((((p1 → (p3 → p3)) → (False ∧ True)) ∧ ((((p1 ∨ True) → p5) ∨ (True ∧ p5)) ∨ p3)) ∧ p3) ∨ p1) → (p2 ∧ p5)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233691301358382761867163415709 : ((p2 ∨ (p2 → p4)) → (p5 → ((p3 ∨ (((p3 ∨ ((True → p5) ∨ p3)) → ((p5 → (p1 → (p4 ∨ p1))) ∨ (p3 ∧ p3))) ∨ p3)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h5
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h8
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h10
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h13
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h16
        -- Implications on the right can always be decomposed.
        intro h17
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h18
        -- One of the premise coincides with the conclusion.
        exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345473970514553399543327329598 : (p3 → (((p5 ∧ (((p4 ∨ (p4 → False)) ∨ p1) ∨ ((p5 ∧ ((p1 ∨ p1) ∨ True)) ∧ ((p3 ∨ p1) → True)))) ∨ ((False → p3) ∨ False)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350132619806321420148858106463 : (p4 → (((((p2 ∨ (p2 → (p5 ∧ p3))) ∨ (p5 ∧ ((False ∧ p3) → p5))) → p5) ∨ (False ∨ (p4 ∧ (((p3 ∧ p2) ∨ p4) ∨ True)))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183913319709146387652353343919 : (((True ∧ (p1 ∧ ((p5 → p4) → ((p1 → False) ∧ p2)))) ∧ False) ∨ ((((p1 ∨ False) ∨ (p4 ∨ (p4 → True))) ∧ p1) → ((p1 ∨ p5) ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
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
theorem thm_5_vars_343321474736041444570887590646 : (p2 → ((p3 ∨ p2) ∧ ((p5 ∨ (((((p3 ∨ p1) → (p1 ∧ ((True → (True → p5)) ∨ p5))) ∧ p2) ∧ False) ∨ True)) ∨ (p4 ∨ (p3 ∧ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47357343726448103943760111444 : ((((p4 ∧ p4) ∨ ((p1 ∧ (p4 ∧ (p2 → p4))) ∧ ((((p1 → False) ∨ p2) ∨ ((True ∨ p1) ∨ p2)) → (p3 → p4)))) ∨ (p2 → p2)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308398246238064250761929170266 : (p2 ∨ (((p5 ∧ (((p4 ∨ p4) ∨ (((((p4 ∨ (p5 → p3)) → p5) ∧ (p3 → p2)) → (False → p1)) ∧ p5)) → (p2 ∧ p2))) ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133691433044851397103284310820 : ((((p1 ∨ (((False ∨ p4) ∧ p1) → (((True ∧ p3) → (p4 ∨ p4)) → (False ∨ p3)))) ∨ ((p5 ∨ p5) → p3)) ∧ p3) ∨ ((True ∨ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52653582888029402555066242375 : (((p1 ∧ ((p4 ∧ (p5 ∨ ((p4 ∨ (p5 ∨ p2)) ∧ p1))) → (False ∧ p2))) ∨ (((((False ∨ p1) → p1) ∨ (p4 ∧ p3)) → p3) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606036199319781122437325478957 : ((((p5 → ((False → p3) → (((((p5 ∨ True) ∧ ((p2 ∨ (p3 ∨ p2)) ∨ (p1 ∨ p1))) ∧ ((p3 ∨ p5) ∧ p2)) ∨ p1) → p1))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214213215235010643541903695413 : ((((p2 → p4) → p4) → p2) ∨ ((((p5 ∨ (p2 ∨ p1)) ∧ p1) → ((p2 → (p5 ∨ (((p1 ∧ False) ∧ p3) ∨ p2))) → p5)) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786207981384735604783694906636 : (((p4 ∨ (((p4 ∧ p3) → (((((p4 → ((False ∨ ((False ∨ p5) → True)) → p5)) ∨ p4) → p1) ∨ p5) ∧ p2)) → (p2 → (p2 ∧ p2)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115673674332857952738914228665 : (((True ∧ ((p1 ∧ (True ∨ False)) ∨ False)) ∨ ((False ∨ True) → (p1 ∧ (((p4 → (False → ((False ∧ True) ∨ p4))) → p3) ∨ False)))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201119572722034253577978172274 : ((True → (p3 ∧ ((p2 ∧ False) ∧ (p1 ∨ p1)))) → (((((p2 → (p1 ∨ (p4 → (p5 ∧ p2)))) ∨ (True ∨ True)) ∧ (p3 ∧ True)) ∨ True) → p5)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h10 := h1 h9
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h5.left
        let h17 := h5.right
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h18 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h19 := h1 h18
        -- We need to get the right conjuct of h19 based on <expert-advice>.
        let h20 := h19.right
        -- We need to get the left conjuct of h20 based on <expert-advice>.
        let h21 := h20.left
        -- We need to get the right conjuct of h21 based on <expert-advice>.
        let h22 := h21.right
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h5.left
        let h25 := h5.right
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h26 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h27 := h1 h26
        -- We need to get the right conjuct of h27 based on <expert-advice>.
        let h28 := h27.right
        -- We need to get the left conjuct of h28 based on <expert-advice>.
        let h29 := h28.left
        -- We need to get the right conjuct of h29 based on <expert-advice>.
        let h30 := h29.right
        -- False on the left can always be used.
        apply False.elim h30
  case inr h31 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h32 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h33 := h1 h32
    -- We need to get the right conjuct of h33 based on <expert-advice>.
    let h34 := h33.right
    -- We need to get the left conjuct of h34 based on <expert-advice>.
    let h35 := h34.left
    -- We need to get the right conjuct of h35 based on <expert-advice>.
    let h36 := h35.right
    -- False on the left can always be used.
    apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113112899480829632568156496669 : (((False → ((True → (((False → False) ∧ p3) → (True ∧ ((p3 ∨ p1) → ((False ∧ p5) ∨ (p4 ∧ p1)))))) ∧ (True → False))) → p3) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198915088276645506788716765543 : ((p3 → (p4 ∧ ((p3 ∨ False) → (p1 ∨ p1)))) ∨ ((p1 → (((((p4 ∨ ((p2 ∨ (p3 ∧ False)) ∨ p2)) ∧ p3) ∧ p4) ∨ p1) ∨ p1)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45822313757020129598971306346 : (((p2 → ((p4 ∧ (((((False → p4) ∨ (p4 → (p5 ∨ (p3 → False)))) ∨ (p4 → p1)) → p4) ∨ (False ∨ (p4 ∨ p4)))) ∨ p3)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157460672906914664680797712557 : ((((((False ∨ (p4 ∧ (True → p4))) → (p2 ∨ (p3 ∨ (p1 ∨ p1)))) ∨ True) ∨ p3) ∨ (p3 ∨ p5)) ∨ (p1 → (p3 ∧ ((True ∧ False) ∧ p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191611356845212777527590579141 : ((p3 ∧ ((False ∧ (p4 ∧ True)) ∧ (p2 ∨ (False ∧ p5)))) ∨ ((((False ∧ (True ∨ p3)) ∨ (p3 → (p2 ∨ True))) ∧ p1) ∨ (True ∨ (p3 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655627405525917211194004097334 : (((((True → (p2 → ((((((True → p2) ∨ True) → (p1 ∨ True)) → True) ∧ False) → (p3 ∧ (False ∧ p5))))) → (p4 ∨ False)) ∨ (False ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_63923922225759506074410515444 : ((False ∨ ((((((p5 ∧ (p1 ∧ (False ∨ (False ∨ (True → (((False → (False → p2)) ∨ p1) ∧ p3)))))) ∧ p2) ∨ p1) ∧ p2) ∨ p5) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_841761461389235860389770514 : ((False ∨ ((p5 ∧ (p1 ∧ (False ∨ (False ∧ p3)))) ∨ (True → ((p5 ∧ (p4 ∨ (p5 ∨ (p4 → ((True ∨ p3) ∧ p5))))) → True)))) ∨ p2) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45508382299541997128874806813 : (((p1 ∨ (((((True ∧ p5) → (p4 ∨ False)) ∧ (p1 → ((p2 ∧ ((p5 → (False → (p3 → p5))) ∨ p2)) → p1))) ∧ False) → p1)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160000275181229157904456450871 : ((((((p2 → p5) ∨ p3) → (False ∧ False)) → ((((p3 ∨ (p5 ∧ p1)) → False) ∨ p2) → p2)) → False) → (p5 → ((p2 ∧ p5) ∧ (False → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((((p2 → p5) ∨ p3) → (False ∧ False)) → ((((p3 ∨ (p5 ∧ p1)) → False) ∨ p2) → p2)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h7 : ((p2 → p5) ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h8
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h9 := h4 h7
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h3
  -- False on the left can always be used.
  apply False.elim h12
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h13
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300187845908798741699690626259 : (False ∨ (((p1 ∨ (((p5 → p3) → (p1 ∧ p3)) ∧ (p3 ∨ ((True ∧ ((p3 ∧ p2) → p5)) ∨ (p3 → (p4 → p1)))))) ∨ p4) → (p2 ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
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
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172774881613488623313146495534 : (((p3 ∨ True) → (p2 → ((p2 ∧ (p3 ∧ p4)) ∨ (((False ∨ True) ∨ p1) ∨ p1)))) ∨ ((True ∧ True) ∧ ((((p3 ∧ False) → p3) ∧ p1) ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
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
  case inr h4 =>
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
theorem thm_5_vars_779539803106682081547316941491 : (((p2 ∨ (((p4 → p2) ∧ ((((((False ∧ (False → True)) ∨ False) ∨ ((p1 ∨ (True → p2)) ∨ p2)) → p5) → p5) ∨ (True ∧ True))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690883934560563000502421825012 : (((((((p1 ∧ (p5 → (p3 ∨ (p1 ∨ True)))) ∨ p2) → (p1 ∨ True)) ∧ (p1 → True)) → (((True → p5) → p4) ∧ ((p4 ∧ p4) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259090565527722151858502957544 : ((True → p5) → ((p4 ∨ (p5 ∧ (p4 ∧ (True ∧ (False ∨ ((False ∨ p1) → p2)))))) → (((True → (((False ∨ False) → p3) ∨ p3)) → p5) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200503856211568940834718960650 : (((p5 ∧ False) → (p1 ∨ ((True → p1) → p3))) → (((True ∨ (p5 ∨ True)) ∧ p3) → (((True ∨ False) ∨ True) → ((p5 ∨ p3) ∧ (True ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h2.left
      let h7 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h7
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h2.left
    let h15 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h2.left
      let h23 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h24 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h27 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h28 =>
      -- False on the left can always be used.
      apply False.elim h28
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h2.left
    let h31 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h32 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h35 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113617168116767132607299660549 : (((True → (((False ∨ ((((p2 ∧ p1) ∧ p5) → p3) → (p1 ∨ p5))) → ((p5 ∧ False) ∧ (False ∧ p4))) ∨ p5)) ∨ (p2 ∧ p5)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248639429944128468998276303430 : ((p3 ∨ p1) ∨ (((p5 ∧ False) ∨ ((False → ((((p2 ∨ (p3 ∨ True)) → p2) ∨ (p5 → p4)) ∧ p5)) ∨ p4)) ∧ ((p5 ∨ p3) ∨ (p5 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114097739448446322639572239238 : (((False ∧ (p3 → (((False ∨ ((((p4 ∧ False) → p3) ∨ p5) → (p2 ∨ True))) ∧ p4) → (True ∧ p5)))) ∨ ((p1 ∨ False) ∨ p1)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314539406816565813278526100221 : (p3 ∨ ((((((p4 → p5) → False) ∧ (((p5 ∨ True) → p4) → False)) → ((p5 → p4) ∨ p5)) → False) ∨ ((p3 ∧ (p3 ∧ p2)) → (p3 ∨ p5)))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129385728998290075981021156826 : (((p5 ∧ ((p4 ∧ (p4 ∨ (p4 ∧ (((p2 ∧ False) ∧ p1) ∨ p4)))) → (((p2 → p2) → p3) → (p4 ∧ p5)))) ∨ True) ∧ ((True ∧ p3) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2598697827227476244686292793 : ((p2 ∨ (((p5 ∧ p1) ∨ (False → False)) ∧ True)) → (p4 ∨ (False ∨ (((True ∨ ((p4 → False) → ((p3 → True) → False))) → False) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184826653722164076073860354590 : ((((p5 ∨ (p4 → p5)) → p1) → ((False ∧ (False ∧ p4)) ∧ True)) ∨ (p1 ∨ (((p3 → p5) ∨ (True ∨ (p2 ∨ (p1 ∧ p1)))) → (False → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658036845764633152170623759076 : ((((p3 ∧ ((((((((p4 → p2) → (False ∨ (p1 → False))) ∨ (True ∧ p5)) → p1) ∨ False) ∨ (p5 ∨ p3)) ∧ p5) ∧ False)) ∨ (True ∨ p4)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_136849760709825215233749861464 : (((p3 ∧ p5) ∨ (((p1 ∧ p1) ∧ (((p5 → p2) ∨ (p3 ∧ (True ∨ p2))) → (p2 ∧ (p2 ∧ p3)))) ∧ (p1 ∨ True))) ∨ (True ∨ (p4 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



