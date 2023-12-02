variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192665647042373658114138980129 : (((((p2 ∧ False) ∧ (p2 → (p1 ∨ True))) → p4) → False) → ((((p5 ∨ p5) ∧ p4) ∨ ((p2 ∧ False) ∧ False)) ∧ ((False → p1) → (False ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∧ False) ∧ (p2 → (p1 ∨ True))) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : (((p2 ∧ False) ∧ (p2 → (p1 ∨ True))) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- False on the left can always be used.
    apply False.elim h15
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h10
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266024507099809736002969405504 : (True ∧ (p1 → ((False → (((p5 ∧ False) ∧ p1) → p5)) ∧ (((((True → (p2 ∨ (((p3 → p1) → p5) ∧ p3))) ∧ True) ∨ True) ∨ p2) ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h7
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
theorem thm_5_vars_63114693491796422451193875237 : ((p5 ∧ ((((p5 ∧ ((p1 ∧ ((p3 ∨ (True ∧ (p2 ∧ p5))) ∨ p5)) ∧ p1)) ∧ ((p5 ∨ ((p5 ∧ p1) ∧ p3)) ∨ p2)) ∨ p3) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606344937356460506814137390632 : (((((((False → (p1 → (((False ∧ (p1 ∨ ((p1 ∧ (True → False)) → p1))) ∧ (p2 ∧ p2)) → (p2 ∨ p1)))) → p1) ∨ False) ∧ p2) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_248038870153875742201397182054 : ((p1 ∨ p5) ∨ ((((p4 → True) ∨ (False ∧ p5)) ∨ (True ∧ (p5 ∧ p4))) → (p1 → (((((p4 ∧ p2) ∧ p5) ∧ p2) ∧ (p5 ∧ p3)) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h6
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608825844513918401983291396599 : (((((((p4 → ((p4 → (p3 → p3)) ∧ (True ∧ (((p4 → p3) ∧ False) ∨ p5)))) ∧ p3) ∧ (((p5 → True) ∧ True) ∨ p3)) ∨ p2) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_167553922240758659611577922483 : (((((p2 ∧ ((False ∧ p5) → p1)) → (True → ((p2 → p2) ∨ True))) ∨ p2) ∨ (False → p5)) → (((p2 → (p5 → (p1 → False))) ∧ p5) ∨ True)) := by
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
theorem thm_5_vars_254726711822035054204816232948 : ((p3 ∧ p3) → ((True → (False ∨ False)) → ((p5 ∧ (((True ∨ (p1 → ((False → p3) ∧ (p2 ∧ True)))) → (p1 → (p5 ∨ p4))) ∧ p4)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654765140227038456108553097191 : ((((((((p1 ∨ ((p2 → (p2 ∨ p3)) ∧ (False → (p3 ∨ p3)))) ∨ p2) ∧ (((False → p2) → p2) → True)) → True) → p2) ∨ (True → True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252631228151096563440586019173 : ((p5 → p4) ∨ (((p4 → (p2 ∧ (((p2 ∨ p5) ∨ p3) ∨ (p1 → (p1 ∨ p2))))) ∨ ((p2 → (p5 ∨ ((True ∨ p1) → p3))) ∨ True)) ∨ p4)) := by
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
theorem thm_5_vars_226179133516563388081499838660 : (((p1 ∨ p3) ∨ p5) ∨ ((p5 ∧ (((True ∧ ((True → (p2 ∨ (True ∨ (False ∨ (p3 ∧ p3))))) → p3)) ∧ p2) → p1)) ∨ (True ∨ (True ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44732640922712827959712203660 : (((((p1 ∧ (True ∨ False)) → p3) ∨ (((((False ∧ (p1 ∧ (True → p1))) → p1) ∧ (p5 ∨ p1)) ∧ (p4 ∨ (p5 ∧ False))) ∧ p5)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124077096838236878967047140062 : (((p2 ∨ (((False ∨ p3) ∧ True) → ((p1 → p2) ∨ (True ∨ p1)))) → ((p1 ∧ ((p1 → (False ∨ p1)) → (False ∨ p4))) ∧ False)) → (p4 ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (((False ∨ p3) ∧ True) → ((p1 → p2) ∨ (True ∨ p1)))) := by
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
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : (p2 ∨ (((False ∨ p3) ∧ True) → ((p1 → p2) ∨ (True ∨ p1)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h10
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193987622734397653100328265037 : ((p3 ∨ (True ∧ (p3 ∧ (p4 → ((p3 → True) ∨ False))))) → (p4 ∨ ((p4 ∧ (((p4 ∧ True) ∨ False) ∧ (True → p4))) ∨ (p1 → (p5 ∨ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166393234329618997106748063134 : ((False ∨ ((p2 ∨ (p5 → p3)) → ((p2 ∨ p2) ∧ (True → ((p2 ∨ (p5 → p4)) ∨ p3))))) ∨ (((True ∧ p5) → (p5 ∨ (p5 ∨ p5))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345318989387184389943778290260 : (p3 → (((((((p4 ∨ False) ∨ ((p2 ∨ ((p4 ∨ p3) ∧ (p4 ∧ (p4 ∨ (p4 → p3))))) → (p1 ∨ p1))) ∨ p3) ∧ p1) → p4) ∧ p4) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64993883062775468923254414422 : ((p2 ∨ (((p4 ∧ p3) ∨ p2) ∨ ((True ∧ ((p1 ∨ (p5 → (((p3 → ((p3 ∨ p2) ∧ p3)) ∨ p1) ∧ p4))) ∧ (p1 → p1))) ∨ True))) ∨ False) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173071262622238881299240255914 : ((False ∨ (p5 ∨ (((True ∧ p3) ∨ (p3 ∧ (p3 ∧ p5))) ∧ (p4 ∧ (p2 → p2))))) ∨ ((p2 ∧ (p3 → (((p4 ∧ p4) → p3) ∨ p3))) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67751892196647601884994741028 : ((p2 → ((((p3 ∨ (p3 ∨ ((p5 ∧ p2) ∧ p1))) → ((False ∨ (p4 → p3)) ∧ (p1 ∧ (p1 ∧ ((p1 ∧ p4) ∧ False))))) ∨ p2) ∨ False)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606743604338735481408006925870 : ((((((False ∧ ((p5 ∧ True) ∧ ((((p5 ∨ (p4 → p1)) ∨ ((p1 → p5) → p4)) ∨ True) ∨ (p5 → True)))) ∨ (p2 ∨ p3)) ∧ False) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_78796729205855149960053098877 : (((((False → False) ∨ ((p4 ∧ False) → True)) → (((p5 ∧ (p1 ∨ (p1 ∨ p5))) ∧ (p3 ∨ (p4 → (p5 ∨ p3)))) ∧ p3)) ∧ (p1 → p5)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((False → False) ∨ ((p4 ∧ False) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207773714438623748226446094758 : (((p3 ∨ (p5 → (p5 ∧ p5))) → p3) → (p2 ∨ ((p2 → (p3 ∨ (False → (p3 ∧ (((p5 ∨ p1) ∧ (p1 ∧ True)) → (p1 ∨ p2)))))) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p3 ∨ (p5 → (p5 ∧ p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66159549852484278770996699150 : ((p5 ∨ (((((p2 ∧ p5) ∨ (((((p2 ∧ p3) ∧ p4) ∨ p4) ∨ p4) ∧ p1)) ∨ (p3 ∧ p5)) ∨ (p2 ∧ p4)) ∧ (p1 → (False → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321065257788627407835610539502 : (p4 ∨ (p1 ∨ ((((p1 ∧ (((p3 ∨ p2) ∨ ((p5 ∨ True) → False)) ∨ False)) ∧ (p4 ∧ (p3 ∨ p4))) ∨ (p5 ∧ False)) ∨ (p3 → (False → p2))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160810720457293276264405694482 : (((p5 → ((False ∨ (p3 ∧ False)) → p4)) ∨ (p1 ∨ ((p1 → (p3 → p3)) ∨ ((p5 → True) ∨ p2)))) → ((p4 ∨ (False ∨ (p5 ∧ False))) → p4)) := by
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h11 =>
            -- One of the premise coincides with the conclusion.
            exact h3
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47705263571247381259389606160 : ((((((((p4 ∧ ((p4 ∨ True) ∧ p1)) ∨ p1) ∧ ((True ∨ p5) ∧ ((False ∧ (p5 ∨ True)) ∨ True))) → p4) ∧ p2) ∨ False) → (p3 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136777207616180443188353886851 : (((True → False) ∧ (p3 ∧ ((p1 ∧ (p3 ∧ ((p4 → p3) ∧ (p5 ∨ False)))) ∧ ((p2 ∧ p3) → ((p2 ∧ p1) → p3))))) ∨ ((False → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593606699582883318290309246098 : (((((p5 → (p1 → (((((True ∧ p5) → (((p2 ∧ False) ∨ False) ∨ (p3 → p3))) ∨ p1) ∨ p4) ∧ False))) → ((True → p2) ∧ p2)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42508379904768606073528758389 : (((False ∨ ((((p3 → p2) ∧ True) ∨ p4) ∨ ((False → (False ∨ (p3 ∨ True))) → (p1 → (p4 ∨ (p2 ∨ ((p2 → p5) ∨ p1))))))) ∨ False) ∨ p4) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303733578978174504502586004461 : (p1 ∨ (((p1 ∧ ((((p3 ∨ (p1 ∧ p2)) ∨ p4) ∧ ((p5 → (False → p3)) ∧ ((p3 ∧ (True ∨ False)) ∧ (True ∨ p1)))) ∧ False)) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354701130091229308321810177498 : (p5 → (((((p1 ∨ True) → (((((True → p2) → ((p3 ∨ True) → True)) ∨ p4) ∧ False) ∨ (False ∧ p2))) ∧ (False → p2)) → (False ∧ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623925310603811974906363326384 : ((((p2 ∨ ((((p4 ∨ (p3 → ((p3 → p5) → (True → p2)))) ∨ (p5 ∧ (p1 ∨ p4))) ∧ (p3 ∨ (p4 ∧ (p1 ∧ p3)))) ∧ p5)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_901076678921659085338366920452 : ((((p5 ∨ (p1 → (True ∧ (((p2 ∨ p4) ∨ (p1 → p1)) ∨ (((p4 → (p4 → p3)) ∧ p5) ∧ (True ∨ p3)))))) → ((p3 ∨ p3) ∧ p1)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ (p1 → (True ∧ (((p2 ∨ p4) ∨ (p1 → p1)) ∨ (((p4 → (p4 → p3)) ∧ p5) ∧ (True ∨ p3)))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56582287163326636114986820148 : (((p1 → ((p2 → p5) ∨ p4)) → ((p3 ∧ ((((((p1 → ((p5 ∧ p3) ∨ p4)) → True) ∧ p1) → p2) ∨ p3) ∨ p1)) ∨ (False ∨ True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324737812165727317672304965855 : (p5 ∨ ((p2 ∧ (p4 → False)) → ((p3 ∨ p5) ∨ ((((p5 ∧ ((True ∧ ((True ∨ p2) → False)) ∨ p4)) ∧ ((p3 → p3) ∨ True)) ∧ p5) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h14 =>
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h15 : (True ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h16 := h13 h15
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h18 : (True ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h19 := h13 h18
      -- False on the left can always be used.
      apply False.elim h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h21 =>
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h22 =>
      -- One of the premise coincides with the conclusion.
      exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231957866938136628455899145673 : (((p1 ∨ p2) → p3) → ((((True → ((((p5 ∨ ((False ∨ p3) ∨ p4)) ∨ False) ∨ ((p1 ∧ (p5 ∨ p2)) → p5)) ∧ False)) → p5) ∨ p1) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_846993562650540339514683904456 : (((((True → p5) ∨ (p5 ∧ (((p4 → (True ∨ False)) → ((p5 → (p1 ∨ p3)) ∨ False)) ∧ ((p5 ∧ False) → (p5 → (p5 ∨ p4)))))) ∨ p5) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h4 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h5 := h3 h4
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752279459819105093753698561314 : (((True ∧ (p5 → (((False ∧ (p2 ∧ (p4 ∧ p2))) ∧ ((False ∧ p3) ∨ p5)) ∨ ((False ∨ ((p1 ∧ ((False → p2) ∧ p3)) ∧ p4)) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657334370212351452911087293258 : (((((False ∨ p4) ∧ (p1 ∨ ((p1 → (((p1 ∨ p4) ∧ ((p1 ∧ (True ∧ p4)) ∧ p4)) → p3)) → ((p1 ∧ p2) ∧ True)))) ∨ (False ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590492086225935944215285970150 : ((((((p3 ∧ p5) → (((p5 ∧ (p5 → (p1 → ((p5 → False) ∨ p4)))) ∨ (((p1 → p1) ∨ p2) ∨ p4)) ∨ (p3 ∨ p2))) → p1) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350956788910926313537900861085 : (p4 → ((((((((True ∨ p4) → True) ∨ (p3 ∨ False)) ∧ (p1 ∧ True)) ∨ p5) ∨ True) → (p1 → ((p2 ∧ (True → False)) ∨ True))) ∨ (p4 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h7.left
        let h10 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h7.left
          let h14 := h7.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h15 =>
          -- False on the left can always be used.
          apply False.elim h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178567413642590842877543745498 : ((((p3 ∨ p4) ∨ ((p1 ∨ True) ∧ False)) ∧ (False ∧ (p5 ∧ (p2 ∨ True)))) ∨ (((p5 ∨ p1) ∨ p1) → ((False ∨ True) ∨ (True ∨ (p4 ∨ p1))))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231486603349776718094682207593 : (((p3 → p2) ∨ p4) → ((((p1 ∧ (p2 ∧ ((True ∧ (p2 ∨ p1)) → (p2 ∧ p5)))) ∧ True) ∨ p3) ∨ (((p5 → True) ∨ (True ∨ p5)) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129117719588556098033421854734 : ((((((p5 ∨ p4) ∨ ((p1 ∨ (p3 ∧ p5)) ∧ (((p3 ∧ p1) ∧ True) ∨ p2))) ∨ (True → (p4 ∧ p4))) → p4) ∨ True) ∧ ((p5 ∧ p2) → p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_345585034762544446793282396195 : (p3 → (((p2 → (p3 ∨ p4)) → (((p2 ∨ p3) ∧ (p1 ∨ (p1 ∧ (p2 ∧ ((p4 → p1) → (((p3 → p2) ∧ p1) → p4)))))) ∨ p1)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1760788622046668276349575485 : ((((False ∨ ((True ∧ p1) ∨ p5)) ∨ ((p3 → (((p5 → (p2 ∨ (p1 ∧ p3))) → p4) → p2)) ∨ p2)) ∧ False) ∨ ((True ∨ p3) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60439064995767720150491750016 : (((p4 → p5) → (True ∧ ((p3 ∧ ((((p1 ∧ p2) ∧ ((p3 → ((p1 → p3) ∨ p3)) ∨ (p4 → p5))) → p5) ∧ (False → p2))) ∨ True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590652274317976967991717505991 : (((((p3 ∧ ((p2 → p1) → (((p3 → ((p2 ∧ (True ∧ p1)) ∧ (True ∨ p1))) ∧ p3) ∧ ((True ∨ False) ∨ (p2 ∧ p1))))) → False) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329186647736618843832066116700 : (True → ((p2 → (p3 → (True ∨ False))) → (((False ∨ (p4 → p2)) ∨ ((p2 ∧ True) → p4)) ∨ ((p1 → ((p2 ∨ (p2 ∧ True)) ∨ p1)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592884495636094485877002080712 : ((((((False ∧ True) ∧ (True → (p3 → (p3 ∧ ((p1 ∨ (((False → p3) → (p5 → p5)) ∧ p1)) ∧ True))))) ∧ ((p5 ∨ True) → p2)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184840334092097726759734203214 : (((p5 ∧ ((p4 ∧ p5) → p2)) → (True ∧ ((p4 → p2) → False))) ∨ ((False ∨ (p3 ∧ ((((p4 → False) ∧ p2) ∧ (p2 ∨ p1)) → True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133972278421652975632254656905 : (((p5 → (True → ((((True ∧ (p2 ∨ (p3 ∨ p4))) ∨ ((p1 ∨ p2) ∧ p5)) → (p1 ∨ (p3 ∨ p5))) ∨ p5))) ∧ False) ∨ ((p2 ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_580454120063577067778390189339 : (((p4 → ((((p3 ∨ True) ∧ (p4 ∧ (p3 ∧ (p3 ∨ ((p1 ∧ p3) ∨ True))))) ∨ ((p5 ∧ False) ∨ (True → p1))) ∨ (False → (False ∨ p4)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646443360930021371830111648454 : ((((p1 → ((p2 ∧ ((((False ∧ ((p3 ∧ (False → p2)) ∨ True)) ∨ (p1 → (p3 ∨ ((False ∨ p3) ∧ p4)))) → p2) ∨ p2)) ∨ p4)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703920675040775903898438747454 : (((((False ∨ ((p5 → (p3 ∧ (p5 → p2))) → p3)) ∨ True) → (p4 ∨ ((p2 ∧ (p4 ∨ (True ∨ p3))) ∨ (((p1 ∨ p2) ∨ p4) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63952018656854189424889927573 : ((False ∨ ((p5 ∧ ((p5 ∨ (p1 ∧ p5)) ∧ (p5 ∨ (p2 → (((p4 ∨ ((True ∨ (False ∧ p2)) ∨ (p2 ∨ p1))) → p2) → p3))))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312123880061604533493608347957 : (p2 ∨ (True → (((p1 → ((False ∨ (p5 ∨ True)) → False)) ∧ (((False ∨ (p4 → p1)) ∧ (p1 ∧ True)) ∧ (p4 → p5))) → (p3 ∨ (p2 ∧ p2))))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h8.left
    let h12 := h8.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h13
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : (False ∨ (p5 ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234218655486858001876874133803 : ((False → (p5 ∧ p3)) → ((False → ((True ∨ (False ∧ p5)) → (((False ∨ p2) → p5) ∨ p5))) ∧ (((False ∨ p3) → p5) → ((False ∨ p3) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260614569595573736588089884499 : ((p3 → p2) → (((False → (p1 → False)) → True) → ((((p5 ∨ p3) ∧ ((True → ((p5 → True) ∧ (p4 → p2))) ∨ p1)) ∨ True) ∨ (p1 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44660458760627380264695393607 : ((((False ∨ (p3 → ((p1 ∧ p2) ∨ True))) ∨ ((p5 → p3) ∧ (False ∨ ((p4 ∧ p4) → ((((True ∨ False) ∨ True) → p3) → p1))))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727413642802740925054891121107 : ((((p3 ∧ (True ∧ False)) ∨ (((True ∨ False) → (p4 → (((p5 → (True ∧ p3)) ∨ p5) ∧ (((p5 → (p3 ∨ True)) ∨ p3) → p3)))) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_689534028801808087416453143566 : ((((((((p2 ∧ p5) → False) ∨ p1) ∨ (p2 ∨ p4)) ∨ (p2 ∨ ((False ∧ p5) → p5))) ∨ (((False → p5) ∧ ((p3 ∧ p5) → p2)) → p5)) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790399661018212488015022545050 : (((p5 ∨ (p5 ∧ (((False ∧ p4) ∨ (p5 → ((p4 ∧ p5) ∧ (p1 → (p5 ∧ (((((True ∧ p4) ∧ p5) ∨ p4) → p5) ∨ p4)))))) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596802239376261058809457974752 : ((((((p1 ∨ (p3 → (True ∧ p1))) ∧ p2) ∨ ((((((p2 ∧ p2) ∧ p3) ∨ p2) → p3) ∨ ((False ∧ p1) ∨ True)) → (True → False))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798614743162000124221117660705 : (((p1 → (((False ∨ (p2 ∨ p1)) ∨ (p5 → p3)) → ((((False ∨ (p2 ∧ False)) ∨ (p2 → p1)) → p4) ∧ ((False → p2) ∨ (p1 ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9676440662249264971942935879 : ((((p4 ∧ p4) ∨ (((p2 → ((p5 ∨ True) → (True ∧ ((True ∨ p5) → p3)))) ∨ p2) → ((((p5 ∨ True) → p3) → True) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157194950870404260224377528405 : (((((p1 ∨ (p4 ∧ False)) → (False ∧ (p5 ∧ ((False → (p1 ∧ p4)) → p3)))) ∧ (p3 → True)) → p3) ∨ (((p2 ∨ True) ∧ (False ∨ True)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215759811386673683197536101251 : ((p1 ∨ ((p4 ∧ p3) ∨ p3)) ∨ ((p5 ∧ (p4 ∧ (True → False))) → ((((True ∨ (p4 ∧ (p3 ∧ (False → False)))) ∧ p4) → (False ∨ p1)) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h1.left
    let h18 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h21 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h22 := h20 h21
    -- False on the left can always be used.
    apply False.elim h22
  -- Conjunctions on the left can always be decomposed.
  let h23 := h1.left
  let h24 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h25 := h24.left
  let h26 := h24.right
  -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
  have h27 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h26, we can now drive its conclusion.
  let h28 := h26 h27
  -- False on the left can always be used.
  apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199831345364563228232907727509 : ((((p2 ∨ p4) ∨ (True ∧ p3)) ∧ (p5 → p2)) → (((False ∨ ((p4 → ((p3 ∨ p3) ∨ p4)) ∨ p4)) ∨ p3) ∨ (p3 ∧ (False ∨ (True → p2))))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136068369708302550990256315642 : ((((p5 ∨ (p3 ∧ p1)) ∨ ((p5 ∧ False) ∧ True)) ∧ ((p3 ∧ (p1 ∨ p5)) → (p5 ∧ (p4 ∧ ((p3 ∧ p2) ∧ p5))))) ∨ (True ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217624857963838488330133834689 : ((((False ∧ p2) → p1) → False) → (False ∨ ((p1 ∧ (((p4 → (p5 ∧ (p3 ∧ False))) → p4) → p4)) ∧ ((p4 ∨ (p4 → (p4 ∨ p1))) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ p2) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54562679982968711155590825515 : (((p4 ∧ ((p4 → False) ∨ (False → (p3 ∧ p4)))) ∨ (True → ((p1 → ((p4 → False) ∧ (((p2 ∧ p4) ∨ (p1 ∧ False)) ∧ p5))) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233188019065891104430798909269 : ((p5 ∧ (p4 ∨ p1)) → ((((p1 ∧ p5) → ((p2 ∧ (False ∨ (False ∨ False))) ∨ p4)) ∧ p4) ∨ (((p1 → p4) ∨ p5) ∧ (p1 ∧ (p3 ∨ p5))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149657948057231365306454332369 : ((p4 ∧ ((p5 ∨ p1) → (p5 ∨ ((((p2 ∨ ((True ∨ (p2 ∧ (p2 → p3))) ∧ p2)) → p5) ∨ p5) → p5)))) ∨ (((p2 ∧ p5) ∨ p5) → p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107129045484043754387418119986 : (((p5 → (p1 → (False ∧ p3))) → (p4 ∨ ((((True ∧ p3) ∧ (p5 ∨ p2)) ∧ (((p5 → p2) → p2) ∧ (p5 ∧ True))) → p3))) ∧ (p4 → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h4.left
    let h11 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h4.left
    let h16 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- One of the premise coincides with the conclusion.
    exact h8
  -- Implications on the right can always be decomposed.
  intro h19
  -- One of the premise coincides with the conclusion.
  exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165257243386956730291818322339 : (((((((p4 ∧ (p1 → (p2 → p3))) ∧ (p1 ∨ p2)) ∧ p4) → True) ∧ True) → (p4 → p2)) ∨ (((p4 ∨ False) ∧ (p4 ∧ p5)) ∨ (True ∧ True))) := by
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
theorem thm_5_vars_58739684906803322760699440289 : (((p3 → p4) ∧ (((True → True) → (((p1 ∧ (p5 ∨ p1)) → True) ∨ p4)) → (((p1 → (p2 ∧ p2)) → p5) ∨ ((p3 ∧ p4) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732714334082389559386384880051 : ((((p1 ∧ p4) ∧ (((p3 ∧ ((((p3 ∧ p2) ∨ (p3 ∨ p4)) → (p5 ∨ (p1 → p4))) → False)) → (p4 ∨ (p1 ∨ (True ∨ p3)))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252421411253007499805151446438 : ((p5 → False) ∨ ((p1 ∨ p2) ∨ ((((True ∧ p3) ∨ p4) → True) ∧ ((p5 → p1) ∨ ((((p2 ∧ p4) ∧ (p2 ∧ False)) ∨ (p5 → p5)) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114170926081210641448743255419 : (((((((p4 ∧ p1) ∧ p5) ∧ True) ∨ (((p2 → (p2 ∧ (p2 ∧ p1))) → p4) ∧ p4)) ∧ (p3 → p4)) → ((p3 ∧ p2) ∧ p5)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115474056718665119934763587666 : (((p5 ∨ (((p5 → False) ∧ p3) ∧ (p3 ∨ False))) ∨ ((True → (p4 ∨ ((p1 ∨ (p3 → p4)) → (p2 → p3)))) → (p4 → p4))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611368260544521251873655932504 : (((((True ∧ ((p1 ∨ (p5 ∧ (((p3 → ((((p3 ∨ (p1 → p4)) ∨ p2) ∧ (p2 ∧ p5)) → p5)) → p4) ∧ p5))) → False)) → p4) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_2279502464550364316019724836 : ((((((p1 → p4) ∨ p1) → p2) ∧ ((p1 ∧ p3) ∧ p2)) ∨ (p5 ∧ True)) ∨ (((p5 ∨ (p1 ∨ (p1 ∨ p5))) ∨ p2) → (True ∨ False))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_914319734984490368359126799827 : (((((((p5 ∨ (p5 ∧ ((p3 ∨ p1) ∨ p3))) → (False ∨ p4)) → p3) → (p3 ∧ p1)) ∧ ((False ∨ p5) ∧ (p4 ∨ ((p1 → p4) ∧ p3)))) → p4) ∧ True) := by
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
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : (((p5 ∨ (p5 ∧ ((p3 ∨ p1) ∨ p3))) → (False ∨ p4)) → p3) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h12
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h16 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h17 := h10 h16
      -- One of the premise coincides with the conclusion.
      exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316658750356565650640378050657 : (p3 ∨ (p4 ∨ (p1 → (((p5 ∨ p2) ∨ (True ∨ ((False → (p5 → False)) → p2))) → (p2 ∨ ((p4 ∨ (p1 ∨ False)) ∨ (p4 → (p4 ∨ True)))))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43589954109136471931161046773 : (((((((p3 ∨ p3) → True) ∨ (p5 ∧ (p4 ∧ ((p5 ∧ (False ∨ (False → p4))) ∧ ((p1 ∧ p1) ∨ (False ∨ False)))))) ∨ p2) → p1) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111828861430131374599784315237 : ((((p3 ∧ ((((((p1 ∨ (p2 → (False ∧ p3))) ∧ (p2 ∧ True)) → p2) ∧ p3) → p1) ∨ False)) ∧ (p2 ∨ (p2 ∧ True))) ∨ p1) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751281752131855316163146216477 : (((True ∧ ((p3 ∨ True) ∧ (((((p4 ∧ False) ∨ (p2 ∧ p4)) ∨ (False ∨ ((p4 ∨ p4) ∨ p2))) ∧ p5) → (((False → p1) → p1) ∨ p5)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190888733448999771511438499992 : (((True ∧ (p5 → (p3 → (False ∨ False)))) → (p3 ∧ p5)) ∨ (True ∨ ((((p1 ∨ (((p5 ∧ p5) ∨ p2) ∧ (p5 ∨ p4))) → True) → p5) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48843648272500972141665085154 : (((p1 ∨ (((False ∨ ((((False ∧ p3) ∨ (p4 ∧ p2)) ∨ p4) → (p1 → p3))) → p2) → (p2 ∧ (p4 → True)))) ∧ (p2 ∨ (p1 → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171492905078211831010759783411 : (((p2 → (p3 ∨ (p2 ∧ (((p3 ∨ (p2 ∧ (False ∨ p5))) ∧ p2) ∧ False)))) ∧ False) ∨ ((False ∧ (p3 ∨ p4)) → ((False ∧ p5) → (p2 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55977155263571099338686517246 : (((((False → True) → False) ∧ p3) ∨ ((True → p3) → (p3 ∨ (((p2 ∧ False) → (p3 ∨ (((p1 ∨ p3) ∨ (p5 ∨ True)) → p2))) ∨ p5)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653757668204545986824615965855 : ((((((p3 → (((False ∨ ((p2 → p4) ∧ ((p5 → (p4 → p3)) ∧ p5))) ∨ True) → (p5 ∨ p3))) → (p4 → False)) ∧ p4) ∨ (False → p1)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_160601182766375054056983040836 : ((((p2 → (False → p4)) → (p3 ∧ (p4 ∧ (True → p2)))) ∧ (((p2 → p1) ∧ p1) → (p5 ∨ p1))) → (True → (p5 → (p3 ∧ (p4 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p2 → (False → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h6
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- One of the premise coincides with the conclusion.
  exact h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h13 : (p2 → (False → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- False on the left can always be used.
    apply False.elim h15
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h16 := h11 h13
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- We need to get the left conjuct of h17 based on <expert-advice>.
  let h18 := h17.left
  -- One of the premise coincides with the conclusion.
  exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71206484794340240142269124678 : (((((True → p3) ∨ p3) ∧ (((((p3 ∧ ((True ∨ p5) → p1)) ∧ p3) ∧ p4) ∨ p1) ∨ (p5 ∧ (((p5 ∧ p1) ∧ p1) → p2)))) ∧ p5) → p3) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h11.left
        let h14 := h11.right
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h15 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h17 := h6 h16
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h21 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h22 := h6 h21
      -- One of the premise coincides with the conclusion.
      exact h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- Conjunctions on the left can always be decomposed.
        let h28 := h26.left
        let h29 := h26.right
        -- Conjunctions on the left can always be decomposed.
        let h30 := h28.left
        let h31 := h28.right
        -- One of the premise coincides with the conclusion.
        exact h29
      case inr h32 =>
        -- One of the premise coincides with the conclusion.
        exact h23
    case inr h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h33.left
      let h35 := h33.right
      -- One of the premise coincides with the conclusion.
      exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321281768306484457485724034923 : (p4 ∨ (p4 ∨ (p1 → ((((((p1 → (True ∨ p4)) → p1) → False) ∨ (p1 → p1)) ∧ False) ∨ (p5 ∨ ((p3 ∧ (False ∨ (p4 → False))) → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214397116051232596588847919989 : (((False → (p5 ∨ False)) → p1) ∨ (((True → ((((p5 → p2) ∨ p2) ∧ p4) ∧ p2)) → (p5 ∨ (p4 ∨ (p1 → ((p3 ∨ True) ∧ p4))))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792877268038529760895555267409 : (((True → (((p5 ∨ p2) → p1) → ((False ∨ (((p5 ∧ (True → False)) ∨ False) ∧ (p4 → (((p2 → p4) → True) ∧ (p5 → p1))))) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41292912423707735455231310599 : (((((True → False) ∧ (((p1 ∧ (p3 ∨ p5)) → p3) ∨ (p4 ∨ ((p1 ∧ True) → (p1 ∧ p4))))) → (p1 ∨ (True ∧ (True → p1)))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206438038602462057198391932194 : ((p4 ∨ ((p1 ∧ (p5 → False)) ∨ p2)) ∨ (((((p5 → p4) → p2) ∧ (p2 ∧ ((p3 → (p3 → p1)) ∧ False))) ∨ p3) ∨ (p3 → (p4 → True)))) := by
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



