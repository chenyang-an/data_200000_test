variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160227011854522607064294835855 : (((((True ∧ ((False ∨ (p4 ∨ p3)) → p1)) ∨ ((p1 → p3) ∧ False)) → (False → p4)) ∨ (p1 → p2)) → (p1 ∨ (p1 → (False ∨ (False → p5))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306017030542210885179718360101 : (p1 ∨ ((p1 ∨ ((p5 → p2) ∨ False)) ∨ (((p3 ∨ ((False ∨ True) ∨ p2)) → (p5 ∨ ((p3 ∨ ((p1 ∧ (p5 ∨ p3)) ∨ False)) ∨ True))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- False on the left can always be used.
        apply False.elim h5
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704232750860897975360797754804 : ((((((p3 → (p5 ∨ p5)) ∧ (p5 → False)) → (p2 → False)) → ((p5 → p3) ∨ (((p1 ∨ True) ∧ p1) → (((p1 ∧ p3) ∧ p5) ∨ True)))) ∨ False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147078638991972432638812088473 : ((((p4 ∧ (((p1 ∨ False) ∧ p2) ∧ p1)) → (((p2 → p5) → p4) → (p5 → ((p4 ∨ p4) → False)))) ∧ False) ∨ (((p3 ∧ p1) → p3) ∨ p1)) := by
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
theorem thm_5_vars_204924780410052507266685747535 : ((((False → p5) ∨ (p5 ∧ p1)) → False) ∨ (p4 → (((True ∨ True) ∨ (p4 → p3)) ∨ (p2 → (True ∨ (((p1 ∨ p1) → (p1 ∨ p1)) ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258793981116367023139883436451 : ((True → False) → (((p1 ∧ p5) ∧ True) ∨ (((p3 → (p4 ∨ p5)) → (((p2 ∨ p1) → (p3 ∨ p4)) ∧ (((p4 ∨ p2) → True) ∨ p1))) ∧ False))) := by
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
theorem thm_5_vars_767188619565193496082128586674 : (((p5 ∧ (((((p5 ∧ (False → (True ∨ (p4 ∧ False)))) ∨ (True ∧ (p5 ∨ (p5 → p3)))) ∧ (False ∧ ((p1 → p2) ∨ p3))) ∧ p1) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64521141166286542628983904777 : ((p1 ∨ ((p4 ∨ (p1 ∨ ((p2 → (p5 ∧ True)) ∨ (p4 → False)))) ∧ ((p3 ∧ ((True ∨ True) ∧ (p5 → (True ∧ p4)))) ∧ (False ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301059710773701312902906947210 : (False ∨ (((p5 → False) ∧ ((p5 ∨ p4) ∧ ((p1 ∧ p2) → p4))) ∨ (((p5 ∨ p3) ∧ p4) ∨ (((p4 → p5) → False) → ((True ∨ p3) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227884571279678986408762481328 : ((p2 ∧ (True → False)) ∨ (((p5 ∧ (((p2 ∨ p2) ∧ ((p2 → (False → p4)) ∨ p3)) ∨ True)) ∧ (False → p2)) ∨ (True ∧ ((p2 → True) ∨ p5)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258035497877879298904058823238 : ((p4 ∨ p2) → ((((p1 → ((True → False) ∨ ((p2 → False) → ((False → p2) → ((False → True) → p2))))) ∧ p1) ∧ ((False → p2) → True)) ∨ True)) := by
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
theorem thm_5_vars_228209002794262842977894543963 : ((p5 ∧ (False ∨ p5)) ∨ (((((p4 → (False ∨ p3)) → (p4 ∧ p5)) ∧ (p1 ∧ (p4 ∧ (p3 ∨ p4)))) → (p5 ∨ (p1 ∨ True))) ∧ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356848483979163106504946713752 : (p5 → ((((False → p3) ∨ False) → p1) ∨ (((p1 → (p1 ∧ (p1 → True))) ∨ (p1 ∨ True)) → (p3 ∨ (((False ∨ p5) ∧ p2) ∨ (False → p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_918930887544985963247102734035 : (((((True ∨ (p1 ∨ (p3 ∧ (p4 ∧ (p5 → (p3 ∧ (p3 ∨ p5))))))) → False) ∧ (((p3 → ((p5 ∧ p4) → p1)) ∧ p3) ∧ (p1 ∨ p1))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : (True ∨ (p1 ∨ (p3 ∧ (p4 ∧ (p5 → (p3 ∧ (p3 ∨ p5))))))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : (True ∨ (p1 ∨ (p3 ∧ (p4 ∧ (p5 → (p3 ∧ (p3 ∨ p5))))))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h12
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233359538178714500297769668618 : ((False ∨ (True ∧ p4)) → (p5 → (((True ∨ p1) → (p4 ∧ (p5 → (((p1 ∨ True) → p2) ∧ ((p2 ∨ ((p2 ∨ p3) ∧ False)) ∧ p1))))) → p1))) := by
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
    have h8 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_914725673515624853999627924609 : (((((False → (p5 → True)) → ((True → ((p5 ∧ False) → (p5 → (True → p3)))) ∧ p5)) ∧ ((p2 → True) → (((p3 ∧ p5) → p5) ∧ False))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317945267590625056791621494961 : (p4 ∨ ((p3 ∨ ((((p4 → p4) ∧ p1) → (p2 ∨ p2)) ∨ (p3 ∨ ((p4 → ((((p5 ∨ p2) ∨ p5) → p3) → False)) → (p2 → True))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148222747903768064832478958804 : (((((p1 → ((((p5 → False) → (p4 ∨ p3)) ∨ p4) → (p1 → p4))) ∨ p1) ∨ p5) ∨ ((p1 ∨ p4) ∨ True)) ∨ (p1 ∨ ((p2 → True) ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233816556219786103183852471651 : ((p3 ∨ (p4 → True)) → (True → ((((False → p4) ∧ p2) ∨ (False ∧ False)) ∨ (True ∨ (((p3 ∧ True) → (True → p2)) ∧ ((True → p3) ∧ p5)))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785578191321149118830940540279 : (((p4 ∨ ((p4 → (((((p1 ∨ p3) ∨ p4) ∧ p3) → p5) → ((((p5 ∨ p4) ∧ p3) ∨ (False → ((p4 ∧ p1) ∨ False))) ∨ p3))) ∨ p3)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630525181731210503693984271586 : (((((p2 ∨ ((((((p1 → ((p5 → p5) → (p4 ∧ p4))) ∨ ((p1 → p4) ∧ (p2 ∨ False))) → p5) ∨ True) ∨ p1) → False)) ∨ p1) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57839906229365890644130942567 : (((p5 ∧ (p1 ∨ p3)) → (((((p5 ∧ (((True ∨ (p4 ∨ (p2 ∧ p5))) → p4) → (p3 ∧ p5))) ∨ p3) ∧ p1) ∨ (False → p3)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793630593506433378715506702747 : (((True → (p4 ∨ ((True → (True ∧ p2)) → ((((p4 ∨ (p3 ∨ p3)) ∨ p3) ∧ (p4 ∧ ((p5 ∨ ((p5 → True) ∨ True)) ∨ p1))) → p2)))) ∨ False) ∧ True) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h5.left
      let h9 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h12 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h13 := h2 h12
          -- We need to get the right conjuct of h13 based on <expert-advice>.
          let h14 := h13.right
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h17 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h18 := h2 h17
            -- We need to get the right conjuct of h18 based on <expert-advice>.
            let h19 := h18.right
            -- One of the premise coincides with the conclusion.
            exact h19
          case inr h20 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h21 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h22 := h2 h21
            -- We need to get the right conjuct of h22 based on <expert-advice>.
            let h23 := h22.right
            -- One of the premise coincides with the conclusion.
            exact h23
      case inr h24 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h25 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h26 := h2 h25
        -- We need to get the right conjuct of h26 based on <expert-advice>.
        let h27 := h26.right
        -- One of the premise coincides with the conclusion.
        exact h27
    case inr h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h5.left
        let h31 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- Disjunctions on the left can always be decomposed.
          cases h32
          case inl h33 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h34 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h35 := h2 h34
            -- We need to get the right conjuct of h35 based on <expert-advice>.
            let h36 := h35.right
            -- One of the premise coincides with the conclusion.
            exact h36
          case inr h37 =>
            -- Disjunctions on the left can always be decomposed.
            cases h37
            case inl h38 =>
              -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
              have h39 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h2, we can now drive its conclusion.
              let h40 := h2 h39
              -- We need to get the right conjuct of h40 based on <expert-advice>.
              let h41 := h40.right
              -- One of the premise coincides with the conclusion.
              exact h41
            case inr h42 =>
              -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
              have h43 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h2, we can now drive its conclusion.
              let h44 := h2 h43
              -- We need to get the right conjuct of h44 based on <expert-advice>.
              let h45 := h44.right
              -- One of the premise coincides with the conclusion.
              exact h45
        case inr h46 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h47 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h48 := h2 h47
          -- We need to get the right conjuct of h48 based on <expert-advice>.
          let h49 := h48.right
          -- One of the premise coincides with the conclusion.
          exact h49
      case inr h50 =>
        -- Conjunctions on the left can always be decomposed.
        let h51 := h5.left
        let h52 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h52
        case inl h53 =>
          -- Disjunctions on the left can always be decomposed.
          cases h53
          case inl h54 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h55 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h56 := h2 h55
            -- We need to get the right conjuct of h56 based on <expert-advice>.
            let h57 := h56.right
            -- One of the premise coincides with the conclusion.
            exact h57
          case inr h58 =>
            -- Disjunctions on the left can always be decomposed.
            cases h58
            case inl h59 =>
              -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
              have h60 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h2, we can now drive its conclusion.
              let h61 := h2 h60
              -- We need to get the right conjuct of h61 based on <expert-advice>.
              let h62 := h61.right
              -- One of the premise coincides with the conclusion.
              exact h62
            case inr h63 =>
              -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
              have h64 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h2, we can now drive its conclusion.
              let h65 := h2 h64
              -- We need to get the right conjuct of h65 based on <expert-advice>.
              let h66 := h65.right
              -- One of the premise coincides with the conclusion.
              exact h66
        case inr h67 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h68 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h69 := h2 h68
          -- We need to get the right conjuct of h69 based on <expert-advice>.
          let h70 := h69.right
          -- One of the premise coincides with the conclusion.
          exact h70
  case inr h71 =>
    -- Conjunctions on the left can always be decomposed.
    let h72 := h5.left
    let h73 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h73
    case inl h74 =>
      -- Disjunctions on the left can always be decomposed.
      cases h74
      case inl h75 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h76 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h77 := h2 h76
        -- We need to get the right conjuct of h77 based on <expert-advice>.
        let h78 := h77.right
        -- One of the premise coincides with the conclusion.
        exact h78
      case inr h79 =>
        -- Disjunctions on the left can always be decomposed.
        cases h79
        case inl h80 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h81 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h82 := h2 h81
          -- We need to get the right conjuct of h82 based on <expert-advice>.
          let h83 := h82.right
          -- One of the premise coincides with the conclusion.
          exact h83
        case inr h84 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h85 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h86 := h2 h85
          -- We need to get the right conjuct of h86 based on <expert-advice>.
          let h87 := h86.right
          -- One of the premise coincides with the conclusion.
          exact h87
    case inr h88 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h89 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h90 := h2 h89
      -- We need to get the right conjuct of h90 based on <expert-advice>.
      let h91 := h90.right
      -- One of the premise coincides with the conclusion.
      exact h91
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147409207020490265870176904387 : ((((p1 ∧ (False ∨ (True ∧ p5))) ∧ ((((p4 ∨ ((False ∧ p3) → p2)) → p2) ∧ (p2 → True)) ∨ True)) ∨ True) ∨ (((p4 → False) → False) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666272677465903010442391189395 : ((((((((p1 → p2) → p1) → p4) ∨ (((p3 → ((p1 ∨ (p4 ∨ p1)) → p5)) ∨ p3) → True)) → (p3 ∨ p1)) ∧ ((p3 → p2) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186308696856217489121162897849 : ((((p3 ∨ ((True → (p2 ∧ p1)) ∨ p5)) ∧ (p4 → p5)) → p2) → ((p4 → (p1 ∨ (p3 → ((p5 ∧ p5) ∨ (False ∨ p1))))) ∨ (False → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45436063850361960557072223429 : (((True ∨ ((True ∨ ((((p5 ∧ ((p4 ∨ p3) ∧ (p1 ∧ p4))) ∧ p4) ∨ (p5 ∨ False)) → ((p5 → True) ∧ p3))) → (p4 ∧ p3))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205053490145196142362256115389 : (((p1 → ((p3 → False) ∨ p4)) → p3) ∨ ((((p2 → (p4 ∧ ((p2 ∧ False) → p4))) ∨ (p2 → (p5 → ((False → p4) → p4)))) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131266643735549115224614955703 : (((((p1 ∧ False) → (p2 → True)) → p4) ∨ ((((p2 ∨ p5) → (p1 ∨ False)) ∧ False) → (p4 ∧ ((False → p3) ∨ True)))) ∧ ((p5 ∨ True) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158303151260328413068295557481 : ((((p2 → p5) → True) → (p1 ∨ (((False ∨ ((p2 ∧ (p5 ∧ (p3 ∨ p5))) ∧ True)) ∧ False) ∨ True))) ∨ ((p5 ∨ (p5 ∧ (p5 ∨ True))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37279193153495950878055575874 : ((((p1 ∨ (((True → p1) ∧ (p2 ∨ ((p5 ∨ True) ∧ (p5 ∧ p5)))) → (True → ((p2 ∨ p1) ∧ (p5 ∨ (False → p5)))))) ∧ p1) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173473984350280328077314763393 : ((((p4 ∨ ((p3 ∧ p3) ∨ ((p1 ∨ ((p4 → False) → p1)) ∧ p1))) ∨ True) ∧ p4) → ((False ∧ False) ∨ ((True ∨ False) → (False → (p2 → False))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Implications on the right can always be decomposed.
        intro h14
        -- Implications on the right can always be decomposed.
        intro h15
        -- False on the left can always be used.
        apply False.elim h14
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- Implications on the right can always be decomposed.
          intro h21
          -- Implications on the right can always be decomposed.
          intro h22
          -- False on the left can always be used.
          apply False.elim h21
        case inr h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h24
          -- Implications on the right can always be decomposed.
          intro h25
          -- Implications on the right can always be decomposed.
          intro h26
          -- False on the left can always be used.
          apply False.elim h25
  case inr h27 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h28
    -- Implications on the right can always be decomposed.
    intro h29
    -- Implications on the right can always be decomposed.
    intro h30
    -- False on the left can always be used.
    apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115003404368479681024028049891 : ((((p3 ∧ ((p4 ∨ p1) ∨ p5)) → (p4 → ((False → True) → p1))) ∧ ((((p3 ∨ p5) ∧ (p2 → p5)) ∨ p4) ∧ (True ∧ True))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139398880478206680371444337108 : (((((p2 ∨ ((p4 → (p1 → ((p2 ∧ p3) ∧ (((p2 → (False ∨ p2)) → False) ∨ True)))) ∨ False)) ∧ p4) ∧ p2) → True) → ((True → p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116896622093352253417155706449 : (((p4 → p3) ∨ (((p4 → (((((p5 ∧ p1) ∧ (True ∨ False)) → p2) → p1) ∨ ((p3 ∨ p3) ∨ False))) → p4) ∨ (p1 → p4))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209215627867531076336821718841 : ((p4 ∨ (p5 ∨ (p5 ∧ (p2 → True)))) → ((True ∨ (((((p4 ∨ p3) ∨ p5) ∧ p5) ∨ (p1 ∧ (p2 → (p1 ∧ p5)))) → p3)) → (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134261266792129485252277185011 : (((((p1 → True) ∧ p2) → ((((p2 → p3) ∨ (((p3 → p1) → True) → (True → (p2 ∧ False)))) ∨ p2) ∧ p2)) ∨ p2) ∨ ((True ∧ p3) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50414462910859432826009666762 : (((p1 ∧ (False ∧ ((((p2 ∨ False) → p1) ∧ (p2 → ((p4 ∧ p4) → p2))) ∨ (False → (p4 ∨ p4))))) ∨ ((p2 ∨ (p5 ∧ p4)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622818499207921637270817970439 : ((((p5 ∧ ((((False → (p3 ∧ (((False ∧ p4) ∨ p4) → (True → p5)))) ∨ (p1 ∧ ((p1 ∨ p5) ∧ (p3 → p5)))) → p2) ∧ False)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_111607641314145823892280133708 : (((((((((p4 ∨ (((False → p3) → p5) ∨ (p4 ∧ p4))) ∧ (p3 ∨ True)) ∧ (p1 ∧ True)) ∨ p3) ∨ p2) ∨ True) ∨ p1) ∨ p4) ∨ (p3 ∧ p4)) := by
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
theorem thm_5_vars_658410015410485195938750313301 : ((((False ∨ (p1 ∨ ((((p2 → p4) ∧ (((p1 → (p4 ∨ False)) ∨ True) ∧ (False ∧ ((p2 → p2) ∧ p5)))) ∧ False) ∨ True))) ∨ (p2 ∧ True)) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749789000117613052418313768416 : (((True ∧ (((p2 → p5) ∨ ((p5 ∧ p5) → ((p1 ∨ (p3 → p4)) → (((p5 ∧ (p3 → False)) ∧ ((p5 → False) ∨ p3)) ∧ True)))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801273516410742953478126394049 : (((p2 → (((True → ((p3 ∧ (True → (p3 ∧ False))) ∨ (True ∧ (p2 ∧ p5)))) ∨ True) ∧ (((p4 ∧ (p4 ∧ False)) ∧ (p2 ∧ p3)) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215197991695054893420847290570 : ((True ∧ (p1 ∨ (False ∧ False))) ∨ (((p1 → (p2 ∧ True)) → (False ∧ p3)) ∨ (p2 ∨ (((p2 ∨ (p2 → (p2 → p3))) ∨ (p5 → p5)) ∨ True)))) := by
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
theorem thm_5_vars_208445605503451800539046831094 : (((True → p4) ∨ (p1 → (False ∨ p1))) → (((False → p5) → p4) → (((((p1 ∨ ((True ∧ True) ∧ True)) ∨ False) ∧ (False → p5)) → p2) → p2))) := by
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
    have h5 : (((p1 ∨ ((True ∧ True) ∧ True)) ∨ False) ∧ (False → p5)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : (((p1 ∨ ((True ∧ True) ∧ True)) ∨ False) ∧ (False → p5)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h9
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225293480700225641225013788978 : (((False ∨ False) ∧ p1) ∨ (p3 ∨ ((((((p4 ∨ (p1 ∨ True)) → p5) ∧ ((p1 ∨ p3) ∨ p2)) → p1) ∧ (p2 → p5)) ∨ ((p5 ∧ False) → p2)))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_15194177435151757571967735318 : (((True → (((False ∧ (p5 → False)) ∨ p5) ∨ (((p4 → (p5 → True)) ∧ p2) ∧ ((True ∨ (False ∨ (p5 → p3))) ∧ p5)))) ∨ (p5 → True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193854764915901161485643905381 : ((True ∨ ((p4 → p4) ∧ (True ∨ ((True ∨ p3) ∨ p3)))) → (((p3 ∧ False) ∨ ((True → p4) → (p3 ∧ (False → (p2 → (p1 ∨ p2)))))) ∨ True)) := by
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
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
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
theorem thm_5_vars_173626796974345080587551698951 : (((False → ((False ∧ ((((p3 ∨ p2) ∧ (False ∧ p4)) ∧ p1) ∧ False)) ∧ p2)) ∧ True) → ((((p2 ∧ p1) ∧ p5) ∧ p4) → ((False → p5) → p1))) := by
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
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174347689391238969058703210694 : ((((((True ∨ p3) ∨ p4) ∧ p5) ∧ ((p1 → p5) ∨ p3)) → ((p2 ∨ p3) ∧ False)) → (((p3 → (p3 ∧ (p4 ∧ (p4 → False)))) ∨ True) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685943773310011714831053853503 : ((((((False → (p5 → (p4 → True))) ∨ (True → (((True ∨ False) ∨ p3) → False))) ∧ (p5 ∧ p4)) → ((p1 ∧ True) ∨ ((p2 ∧ p1) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695598691175740813377334063149 : (((((((p1 ∧ (p2 ∨ p1)) ∨ p3) → False) ∧ (p1 ∧ (p4 → (p4 ∧ p4)))) → (((p3 ∧ ((False ∨ p2) ∨ (p5 ∨ p1))) → p3) ∧ p2)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h1.left
      let h15 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h1.left
      let h20 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- One of the premise coincides with the conclusion.
      exact h3
  -- Conjunctions on the left can always be decomposed.
  let h23 := h1.left
  let h24 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h25 := h24.left
  let h26 := h24.right
  -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
  have h27 : ((p1 ∧ (p2 ∨ p1)) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h25
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h25
  -- We have shown the premise of h23, we can now drive its conclusion.
  let h28 := h23 h27
  -- False on the left can always be used.
  apply False.elim h28
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252589166345507874692403154722 : ((p5 → p3) ∨ (((p5 ∧ (p1 ∧ True)) ∨ (p1 ∧ (((p5 ∧ ((False → p5) ∧ False)) ∨ p1) ∧ False))) ∨ ((True ∨ ((p1 ∧ True) ∧ p2)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356611681911911265974211480382 : (p5 → ((((True → ((p2 ∨ p5) → p5)) → p3) ∧ p4) ∨ ((p3 ∨ ((p4 ∨ p3) ∨ (p5 → (((p3 ∨ p1) ∨ False) ∧ (p5 ∨ p4))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20290735690711027172905312220 : (((False ∧ (p5 ∨ ((p1 ∧ True) → (p2 ∨ (p5 → (p2 ∨ (p2 ∨ True))))))) ∨ ((((True → p5) → p1) ∧ ((False ∨ p3) ∧ p5)) → p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184843359670395548921888633790 : (((p2 ∨ ((p4 ∧ True) → p2)) → (p5 → ((True → False) ∨ p3))) ∨ (((((p4 → ((p1 → False) ∨ False)) ∧ p1) → (p5 ∧ True)) ∧ False) → False)) := by
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
theorem thm_5_vars_118896245793695798885686925365 : ((True → (p1 ∨ ((((((p2 ∨ ((True ∧ p1) ∨ (p5 ∨ p3))) ∧ (p3 → True)) ∨ True) ∨ p4) ∧ (p2 → p1)) → (p2 ∨ False)))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346369140327058884666819215274 : (p3 → ((p1 ∧ ((p3 → p1) ∨ (p5 → (p1 ∨ (p3 ∧ ((p4 ∧ p4) → ((p1 ∨ (((True ∨ True) ∧ True) ∧ p2)) ∨ p2))))))) ∨ (False → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64406279584998447873833546133 : ((p1 ∨ (((((p1 ∧ p2) ∨ False) ∨ (p2 → p5)) ∨ ((((((True ∨ (p4 ∨ p4)) ∧ p2) ∧ (p5 → p1)) ∨ p3) ∧ p4) → p3)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57465997117369430259511763306 : (((True → (p3 ∨ False)) ∨ ((((((p3 ∨ True) → (((True ∨ p5) ∧ (p2 ∧ True)) ∨ (p2 ∨ p1))) → (p1 ∧ p5)) ∨ p2) ∧ p3) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710996825566929447660285747695 : (((((p5 ∧ True) → ((True ∨ p5) ∧ p2)) ∧ (True ∧ ((p3 ∧ p3) ∨ ((False → True) → (p2 ∨ ((p2 → (False ∨ p1)) → (p2 ∨ p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327859801041816291537917216799 : (True → (((p5 → (p5 ∨ False)) ∧ (p3 ∨ (((False ∧ p2) → (p2 → p3)) ∧ (p1 ∧ (((p1 → False) ∧ p3) ∨ (p2 ∧ True)))))) ∨ (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180703297490655461602469516789 : ((((p2 ∧ (p5 ∨ p5)) ∨ False) ∧ (True ∨ ((p5 ∨ p3) ∧ (p1 ∨ p1)))) → (((p2 → False) ∧ p2) ∨ (((p1 → False) ∧ (False ∧ p4)) → p3))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- False on the left can always be used.
        apply False.elim h12
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h19
            -- Conjunctions on the left can always be decomposed.
            let h20 := h19.left
            let h21 := h19.right
            -- Conjunctions on the left can always be decomposed.
            let h22 := h21.left
            let h23 := h21.right
            -- False on the left can always be used.
            apply False.elim h22
          case inr h24 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h25
            -- Conjunctions on the left can always be decomposed.
            let h26 := h25.left
            let h27 := h25.right
            -- Conjunctions on the left can always be decomposed.
            let h28 := h27.left
            let h29 := h27.right
            -- False on the left can always be used.
            apply False.elim h28
        case inr h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h31 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h32
            -- Conjunctions on the left can always be decomposed.
            let h33 := h32.left
            let h34 := h32.right
            -- Conjunctions on the left can always be decomposed.
            let h35 := h34.left
            let h36 := h34.right
            -- False on the left can always be used.
            apply False.elim h35
          case inr h37 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h38
            -- Conjunctions on the left can always be decomposed.
            let h39 := h38.left
            let h40 := h38.right
            -- Conjunctions on the left can always be decomposed.
            let h41 := h40.left
            let h42 := h40.right
            -- False on the left can always be used.
            apply False.elim h41
    case inr h43 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h44 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h45
        -- Conjunctions on the left can always be decomposed.
        let h46 := h45.left
        let h47 := h45.right
        -- Conjunctions on the left can always be decomposed.
        let h48 := h47.left
        let h49 := h47.right
        -- False on the left can always be used.
        apply False.elim h48
      case inr h50 =>
        -- Conjunctions on the left can always be decomposed.
        let h51 := h50.left
        let h52 := h50.right
        -- Disjunctions on the left can always be decomposed.
        cases h51
        case inl h53 =>
          -- Disjunctions on the left can always be decomposed.
          cases h52
          case inl h54 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h55
            -- Conjunctions on the left can always be decomposed.
            let h56 := h55.left
            let h57 := h55.right
            -- Conjunctions on the left can always be decomposed.
            let h58 := h57.left
            let h59 := h57.right
            -- False on the left can always be used.
            apply False.elim h58
          case inr h60 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h61
            -- Conjunctions on the left can always be decomposed.
            let h62 := h61.left
            let h63 := h61.right
            -- Conjunctions on the left can always be decomposed.
            let h64 := h63.left
            let h65 := h63.right
            -- False on the left can always be used.
            apply False.elim h64
        case inr h66 =>
          -- Disjunctions on the left can always be decomposed.
          cases h52
          case inl h67 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h68
            -- Conjunctions on the left can always be decomposed.
            let h69 := h68.left
            let h70 := h68.right
            -- Conjunctions on the left can always be decomposed.
            let h71 := h70.left
            let h72 := h70.right
            -- False on the left can always be used.
            apply False.elim h71
          case inr h73 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h74
            -- Conjunctions on the left can always be decomposed.
            let h75 := h74.left
            let h76 := h74.right
            -- Conjunctions on the left can always be decomposed.
            let h77 := h76.left
            let h78 := h76.right
            -- False on the left can always be used.
            apply False.elim h77
  case inr h79 =>
    -- False on the left can always be used.
    apply False.elim h79



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191934801006938758153813015280 : ((True → (((False ∧ True) → (p5 ∨ p2)) → (p4 ∨ p3))) ∨ ((p5 ∨ ((p3 ∧ (p2 → ((p3 ∨ (p5 ∧ p5)) ∧ (p5 → p4)))) ∧ p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731698823320502676849324461480 : ((((p2 → (p3 ∨ p3)) → (((p2 → ((p4 ∨ p1) ∨ ((True → p4) → (False ∨ p5)))) ∨ ((p5 ∧ p2) ∨ ((p5 ∧ p1) → p1))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618447328064910228297442891078 : (((((((p5 ∨ p3) → p2) ∨ p3) → ((((False ∧ True) ∨ p5) ∧ ((p2 ∧ True) ∧ (p3 → (p4 → (False ∧ p1))))) ∨ (p1 ∨ p4))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591639126215945274693748089274 : ((((((((p2 → (p4 ∧ p3)) ∨ p5) ∧ ((((False ∨ (p1 → (p1 ∨ True))) → p5) ∧ (p1 ∧ True)) ∨ True)) ∧ p2) ∨ (p5 ∧ True)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61624797266085051850596155397 : ((p1 ∧ ((p3 → p1) ∨ (((((p5 ∧ (False ∨ p3)) → True) ∨ (((p5 ∧ (True → (False ∧ p3))) ∨ p1) ∨ p4)) ∨ (p5 → p1)) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46790023666642799008816712711 : (((p5 → (((((p2 ∨ p3) ∧ (((True → p1) ∨ ((p5 ∧ ((p2 ∨ p4) ∧ True)) → p3)) ∧ p5)) → True) → p1) ∨ p5)) ∧ (p2 ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336224468295228068195354136239 : (p1 → (((((True ∨ False) → (p4 → ((True ∨ (p2 ∨ p3)) ∧ (((p3 ∧ False) ∨ p2) → (p1 ∨ False))))) → p4) ∨ ((p3 ∧ True) ∨ True)) ∨ p5)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149380396294173811421569099947 : (((p3 → p2) → ((p2 ∧ p3) ∧ (((True ∨ (True → (p2 ∨ p1))) ∨ (p5 ∨ ((p3 → p3) ∧ p2))) ∨ p2))) ∨ ((p2 → (False ∨ True)) ∨ p5)) := by
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
theorem thm_5_vars_798591341376815074235464187976 : (((p1 → (((p3 ∧ p5) ∧ (False ∨ (True ∨ p2))) ∨ ((((p1 ∨ (p1 ∧ ((((False ∨ False) → p3) → False) ∧ p1))) → p1) ∧ p3) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665226101201021999152011907 : (((p3 → ((p1 → ((True ∨ (((p2 ∧ True) → p3) ∨ (p1 → p3))) → p5)) ∨ (False ∨ p2))) ∨ ((p4 ∧ (p1 ∧ False)) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804050903507631308421897791052 : (((p3 → (((p5 ∨ ((p1 ∨ (p1 ∨ (False ∨ p4))) → (p4 ∧ (p1 → True)))) ∧ (((p2 ∨ False) → p4) ∨ p2)) → ((p3 ∨ p3) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_938121380998506963599968577265 : ((((p2 → ((True → (p3 ∧ p1)) ∧ p4)) ∧ (p1 ∧ (p2 ∨ (((((p3 ∨ (False ∨ p5)) ∨ (p4 ∨ p4)) ∧ (p4 ∧ p5)) ∧ p5) ∧ p3)))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h13.left
        let h17 := h13.right
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h13.left
          let h22 := h13.right
          -- One of the premise coincides with the conclusion.
          exact h4
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h13.left
        let h26 := h13.right
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h13.left
        let h29 := h13.right
        -- One of the premise coincides with the conclusion.
        exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173308386153922080484847386928 : ((p1 → (p5 ∧ ((p4 ∧ p3) ∨ ((p4 ∨ (p1 → False)) → ((p3 → p3) → p3))))) ∨ (p1 ∨ ((p5 → (((p3 → p3) ∧ False) ∨ p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300069730266824230213899373413 : (False ∨ (((p1 ∨ (((p4 ∨ (False ∧ (((p4 ∧ p3) ∨ p5) → ((p1 ∨ p5) → p1)))) ∨ (True ∨ True)) → (p5 ∨ p2))) ∨ True) ∨ (p2 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157399069487318422015449827321 : (((((False ∨ (False → ((p5 ∧ (p3 ∨ (True → p5))) → False))) ∨ p2) ∧ (p4 ∧ p5)) ∧ (p2 → p4)) ∨ ((False → p2) → (False ∨ (True ∨ p5)))) := by
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
theorem thm_5_vars_316366537223278205245169242767 : (p3 ∨ (False ∨ ((((p5 ∨ (((p3 ∨ ((False → p4) ∨ p3)) → (p4 ∧ False)) ∨ (p1 → (True ∧ p4)))) ∨ p2) → (False ∨ (False ∨ p5))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327238292107839689321969571174 : (True → ((p4 → (p5 ∨ ((((p4 → (p5 → p1)) ∨ ((((p2 → p2) ∨ (False → p5)) → (False ∧ True)) ∨ p1)) ∨ (p3 ∨ False)) ∨ True))) ∨ p1)) := by
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
theorem thm_5_vars_259294670590438232746327834972 : ((False → p1) → (p2 ∨ (((True ∧ (((p2 ∧ p5) ∨ ((False → (p1 ∨ False)) ∧ p3)) ∧ (False ∨ True))) → False) ∨ (True → (p2 → (True ∧ True)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713844124900621183525283203445 : ((((((p4 ∨ (True → p3)) → p3) ∨ p5) → ((p1 ∧ (True ∨ ((p2 ∨ (p3 ∨ True)) ∧ p2))) ∨ ((True → (p5 ∨ False)) → (p5 → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786688647274922097864122821766 : (((p4 ∨ (((p2 ∨ p3) ∧ ((p5 → True) ∨ p4)) ∨ ((False ∧ ((p5 ∨ p2) → ((p5 ∨ ((p2 → p4) ∧ (p4 → True))) ∧ True))) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60597717081626263930275538353 : ((True ∧ ((p5 → (((False ∧ (p5 ∧ ((p2 → (((p1 ∨ (p5 → p1)) ∧ True) ∧ p1)) ∧ False))) → (p1 ∨ True)) ∨ (p4 → p4))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112613390525981918860990204759 : (((((((p2 ∨ p4) ∨ (p1 ∧ p2)) ∨ (False ∨ True)) → ((False ∧ p2) → ((p3 ∨ p5) ∨ (False → p5)))) ∨ (p2 ∨ p4)) → False) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53544178595799989433988484273 : ((((((p5 → p2) → p1) ∧ ((p1 ∧ p4) → p3)) ∧ False) ∧ (p5 ∨ ((False ∧ p4) → (((p1 ∨ (p4 ∨ p2)) → p5) → (p5 ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341014944698675720552263260205 : (p2 → ((p2 ∧ ((((((p2 → True) → (p2 ∨ p2)) ∧ ((p5 → p1) ∨ p4)) ∧ p4) ∨ p4) ∨ (p5 ∧ ((p5 ∧ (p5 ∨ p5)) ∧ p1)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694782987929839395683272789907 : ((((True → (((p1 ∨ ((p4 → True) ∧ (False ∧ p3))) ∧ (p1 ∨ p2)) ∧ p4)) ∨ ((True ∨ ((p2 ∧ (False ∨ p1)) ∧ (False → p5))) ∧ True)) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129080006848791643973351431744 : (((((((p5 → False) → False) → (p4 ∨ False)) ∨ (((p5 → (((False ∨ p5) → p1) ∧ p3)) → p1) → False)) ∨ True) ∨ p2) ∧ (p1 ∨ (True ∧ True))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703195721585025301105009345130 : ((((False ∧ ((((False ∧ p2) ∧ p2) → (True ∧ p3)) ∧ p5)) ∨ (((True → p3) → (((((False → p5) ∨ p1) ∧ p4) → False) → p1)) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_196914314257827537339586909081 : (((((False → (False ∨ p5)) ∨ p5) ∧ p2) ∨ p2) ∨ ((((True → (p4 ∧ (p2 → ((p4 → (p4 ∨ p3)) ∨ (False ∧ p5))))) → p2) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42251780016884876524039561220 : (((p1 ∧ (((p5 → (True → p5)) ∧ (((p1 ∨ p2) ∨ ((p2 ∨ p5) → ((p3 ∨ True) ∨ ((p5 ∧ p3) ∨ False)))) ∧ p4)) ∧ p4)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777013506781539194193681883683 : (((p1 ∨ ((((p3 ∨ (p3 ∨ p3)) → (((p4 ∧ (p3 ∨ p2)) → (p4 ∨ (True ∧ ((True → True) → p4)))) → False)) ∧ False) ∨ (p5 ∨ True))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219009187245347307123202291931 : ((p4 ∧ (True → (True → False))) → (((p4 ∧ ((p5 → (((p1 → ((p3 → p5) ∧ p1)) → (p1 → p4)) ∨ (False ∨ p5))) ∨ p2)) → p2) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609028108718777541345734213591 : ((((((False ∨ ((p4 ∨ p2) → (p3 → (p3 → (p5 ∨ p2))))) → ((p4 ∨ (False ∨ (p5 ∧ True))) → (False ∧ (p4 → p1)))) ∨ p1) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_41520401575241493913706281836 : (((((p5 ∧ (p1 ∨ p2)) ∧ (p5 ∧ ((p2 → False) → p4))) ∧ (p4 → ((False ∧ ((p4 ∧ (p5 ∧ False)) ∨ (p3 → p4))) ∧ p4))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64265123603307482067314264463 : ((False ∨ (p5 ∨ (False ∧ ((((p5 → (((p3 → p1) → (p1 → True)) → (p3 ∧ p4))) → p4) ∨ (False → (p3 ∨ p2))) → (False ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217743338663600117554261796833 : (((p3 ∧ (p4 ∧ True)) → p2) → (True ∧ (p3 ∨ (((((False ∨ p4) ∨ True) ∨ p5) → p5) → (((((p2 ∧ False) ∧ p2) ∨ p5) ∨ p4) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((False ∨ p4) ∨ True) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155081366282512871030892154414 : (((p1 ∧ (p3 ∧ ((p5 ∧ p5) ∧ ((p2 ∨ p5) → (p1 ∧ False))))) → (((p1 ∨ p1) → p4) ∧ p2)) ∧ ((p4 ∨ p2) → ((False → p5) ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    let h4 := h1.left
    let h5 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h12 : (p2 ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h13 := h9 h12
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h1.left
    let h17 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h24 : (p2 ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h23
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h25 := h21 h24
    -- We need to get the right conjuct of h25 based on <expert-advice>.
    let h26 := h25.right
    -- False on the left can always be used.
    apply False.elim h26
  -- Conjunctions on the left can always be decomposed.
  let h27 := h1.left
  let h28 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h29 := h28.left
  let h30 := h28.right
  -- Conjunctions on the left can always be decomposed.
  let h31 := h30.left
  let h32 := h30.right
  -- Conjunctions on the left can always be decomposed.
  let h33 := h31.left
  let h34 := h31.right
  -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
  have h35 : (p2 ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h34
  -- We have shown the premise of h32, we can now drive its conclusion.
  let h36 := h32 h35
  -- We need to get the right conjuct of h36 based on <expert-advice>.
  let h37 := h36.right
  -- False on the left can always be used.
  apply False.elim h37
  -- Implications on the right can always be decomposed.
  intro h38
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h39
  -- False on the left can always be used.
  apply False.elim h39
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40990553882693755690668783710 : ((((p1 ∨ ((((p5 ∨ p3) → (True → p1)) → (p5 → (True ∧ (p2 ∧ p1)))) ∧ (((p5 → p4) ∨ p2) → p3))) ∨ (False → p2)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



