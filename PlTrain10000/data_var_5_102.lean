variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65044177960297346730412088204 : ((p2 ∨ (False ∧ ((p4 ∨ ((p5 ∨ p3) ∧ ((False ∨ p1) ∨ (p2 → (p4 ∨ (((p1 → (True → True)) → p3) → (False ∨ p4))))))) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60727365178910935157490606299 : ((True ∧ (((False ∨ (p2 ∧ p5)) ∨ p1) ∨ ((((((True → p5) → p5) → p5) ∧ (p5 → False)) ∧ p5) → ((p5 ∧ (p3 ∨ p1)) → p2)))) ∨ p5) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h17 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h18 := h16 h17
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192816749825406334537700353871 : (((p2 → ((p3 → (p1 ∧ p2)) ∨ (p5 ∨ True))) → False) → (((p3 ∧ (p3 → p2)) ∧ False) ∨ (((p1 → (p4 → (False ∧ p4))) ∧ False) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → ((p3 → (p1 ∧ p2)) ∨ (p5 ∨ True))) := by
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
theorem thm_5_vars_700243579323928465711937163651 : (((((True → False) → ((p2 ∧ (p5 → True)) → (p2 ∧ (True ∧ p1)))) → ((True ∧ ((p4 ∨ (p1 → ((p5 → p5) ∨ p3))) → p1)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351541821912846255895814585371 : (p4 → ((True ∧ (((p1 ∧ (p5 ∨ p5)) ∨ ((p3 ∨ p1) ∧ False)) ∨ (p5 → (p1 ∨ (p5 ∨ p5))))) ∨ ((p3 ∨ False) → (p2 → (p4 ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710298903932825579017598173963 : (((((p1 → ((False → p1) → False)) ∨ p3) ∧ ((p1 → (p4 ∧ (p4 ∧ ((p2 → p3) → (p2 → p3))))) → (p2 ∧ ((p4 ∨ p5) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179856545797748171891043047160 : (((True → ((((p3 ∨ (p3 ∨ p3)) ∧ p1) ∧ (True ∨ p3)) ∨ p5)) ∧ p5) → (((p1 ∧ ((p1 ∨ p4) ∨ False)) ∨ (p4 → (p2 ∨ p4))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312228040405341388480155518092 : (p2 ∨ (p1 → (((p1 ∧ ((p2 ∨ (((False ∨ p5) → ((p2 ∧ (p5 ∨ p3)) → (((p3 ∧ False) → False) → False))) → p2)) → p4)) ∨ p1) ∨ p3))) := by
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
theorem thm_5_vars_150254501690844205910573939786 : ((p3 → ((p2 ∨ (((False → ((p4 → p5) → True)) ∨ p4) → False)) ∨ ((p3 ∨ p1) → ((p3 ∧ p1) ∨ True)))) ∨ (p3 ∧ ((p5 → p3) → p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613875317041501990620677425418 : (((((((p3 ∨ p3) ∨ (p2 ∧ ((p2 ∨ ((p1 → p4) ∨ p3)) ∧ (p5 → (False → (p1 ∧ p3)))))) ∨ p5) ∨ (True ∧ (p5 → p3))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217018938403819401280544145692 : ((((p3 ∧ p2) ∧ p4) ∨ p3) → ((p2 → ((((p1 ∧ p4) ∨ (False ∧ (p2 → (p4 ∨ p4)))) ∧ p3) ∨ p3)) ∧ ((True ∨ (p1 ∨ p1)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136729354950065199770939516447 : (((p5 ∧ p3) ∧ ((((((p5 ∨ (True → ((p3 ∨ p4) → p3))) ∨ (p4 ∧ p2)) ∧ p2) → (p3 ∨ False)) ∧ p5) ∧ p4)) ∨ (True ∨ (p3 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730856376124291434978398343822 : ((((p5 ∧ (p5 ∨ False)) → (p1 → ((p4 ∨ (True → p4)) ∧ (p2 ∨ ((((p2 ∨ p4) ∨ p4) ∨ ((False → p1) ∧ p3)) ∨ (p4 → False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345835007367257253914522698765 : (p3 → (((((True → (p1 ∨ ((False ∧ p4) ∧ (p4 ∨ False)))) ∨ False) ∨ (((p5 ∧ p1) ∨ p3) ∨ (((p1 ∨ p3) → p3) ∨ False))) → p2) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((True → (p1 ∨ ((False ∧ p4) ∧ (p4 ∨ False)))) ∨ False) ∨ (((p5 ∧ p1) ∨ p3) ∨ (((p1 ∨ p3) → p3) ∨ False))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118514742149225541295717980292 : ((p3 ∨ (((p4 ∧ True) ∨ p5) ∨ (((((((True ∧ (False ∧ p5)) → p2) → p5) ∨ p1) ∧ (p2 ∧ p1)) ∧ (p3 → False)) → p4))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165650740507712932239356967244 : ((((False ∧ (p5 ∧ (p1 ∨ p1))) ∨ p4) ∨ (p3 ∨ ((p5 → False) ∨ ((True ∨ p2) ∨ p5)))) ∨ (p1 → ((True ∧ p4) → ((False ∧ p4) ∨ p5)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741296548703466887278622625367 : ((((p4 ∨ p5) ∨ ((p5 ∧ (((p1 ∧ True) → (p4 ∧ (p4 → p3))) ∧ (p3 ∧ (True → (p2 ∨ ((False ∧ True) → (True ∨ p1))))))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148027120745016428852154928771 : (((((False → (True ∧ p5)) → p4) ∨ (((True → (p5 → p1)) ∧ False) ∧ ((p3 ∧ True) ∨ p5))) ∨ (False → True)) ∨ (((p4 → False) → p1) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158691937631993536697047005173 : ((p2 ∧ ((p3 ∨ False) → (False ∨ (p5 ∧ ((p3 → p1) ∨ (((p4 → (p5 → True)) ∨ p2) → p2)))))) ∨ ((True ∨ (p1 ∨ (p2 → True))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801229090539818186465516913476 : (((p2 → ((((((p3 ∨ True) → True) → False) ∧ ((p2 ∧ False) ∧ p2)) ∨ ((p1 ∧ p2) ∧ p2)) ∨ ((p3 → p2) ∨ ((p1 → p1) ∨ False)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40341517155673069752406940390 : (((((True ∧ ((p2 ∧ (((False → p3) → ((p1 ∧ (p5 ∨ (True ∨ True))) → False)) → p4)) → (p5 ∧ (True → True)))) ∨ p4) ∨ p4) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158523911433658180844953608046 : (((p4 ∨ p4) → ((((True ∧ (((p3 ∨ p2) ∨ (True ∧ True)) ∧ (True → False))) ∨ True) ∧ p1) ∨ True)) ∨ (((False ∧ p3) → p5) ∨ (p3 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175371048999813768604766445123 : ((True → ((((p1 → (False ∧ True)) ∨ (p5 ∧ p5)) ∧ (True → (p5 ∧ p4))) ∨ p1)) → ((p1 ∨ (p2 ∨ p5)) ∨ (True ∧ (p3 ∨ (p2 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h9 := h6 h8
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330721202547466726609798498671 : (True → (p1 → ((((((((True → (False ∨ p4)) ∨ (p3 → p3)) ∧ (p4 → False)) ∨ False) ∧ ((p1 ∨ p5) ∨ True)) ∨ p3) → (p5 ∧ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609857162347462634525212816391 : (((((p1 → ((False → (p4 ∧ ((True ∧ (p1 ∧ p1)) ∨ p3))) ∧ (((p4 → p2) ∨ p1) → (p3 ∨ ((False ∨ False) ∨ True))))) ∨ False) ∨ False) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68914871080373640367613411987 : ((p4 → (p1 ∨ ((((p1 ∨ (p1 → p5)) → ((p4 ∨ (p1 → p4)) ∧ (((p4 ∧ False) ∨ p5) ∧ p3))) ∨ ((p5 → p5) ∧ True)) ∧ p4))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57195015968971219016560116073 : ((((p3 ∨ p4) ∨ p4) ∨ ((False → p3) → ((True ∧ p4) ∨ (p4 → (p2 ∧ (((False ∧ (p1 ∧ (False → p2))) ∨ (True ∨ p5)) → p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616971896487383760810827765656 : ((((((((p2 ∨ (True → p5)) ∨ False) ∧ p3) ∧ p3) ∧ ((p4 ∨ True) → (p1 ∧ (p2 ∧ ((((True ∧ p3) ∧ p3) → p3) → True))))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_9689071112340713893806176870 : ((((p1 ∨ False) ∨ (((p2 ∨ p3) ∧ ((p3 ∨ p1) ∧ p1)) ∧ ((p4 ∧ (p4 → (((True ∧ (False → p5)) ∧ p1) ∨ p1))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53815043630503615132264450383 : (((((False ∧ False) → ((p5 ∧ p2) ∨ p5)) ∧ (p2 ∧ p2)) ∨ (((p4 ∨ ((True → p2) ∧ (((p2 ∧ p2) → p4) ∨ p1))) ∧ False) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801247026894091710419007721984 : (((p2 → ((((((p2 → ((p4 ∧ ((p5 ∧ p3) ∨ p3)) ∧ True)) ∧ p2) ∨ p2) → p3) ∨ False) → ((p5 → (p2 → (False ∨ False))) ∨ p3))) ∨ p1) ∧ True) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (((p2 → ((p4 ∧ ((p5 ∧ p3) ∨ p3)) ∧ True)) ∧ p2) ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47487081933502860503347444077 : (((False ∨ ((True → ((((p5 → False) → p5) → (p5 ∨ ((p2 ∧ (p5 ∨ (p4 ∨ p2))) → p3))) ∨ p5)) → (p5 ∧ p2))) ∨ (p1 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141512153807667611066056015344 : ((((p1 ∧ True) ∨ True) ∨ ((p3 → p5) ∨ (p2 ∧ (p4 → (((True ∨ ((p3 → (p5 ∨ p2)) ∨ p2)) ∨ True) → p1))))) → (p4 ∨ (p3 ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213360020240551283410367558103 : (((p4 ∧ (p3 ∨ True)) ∧ p4) ∨ (((p2 ∨ (p4 → p1)) → (p5 ∧ ((p2 ∧ (p3 ∧ (((False ∧ p1) ∨ p1) ∨ p1))) ∨ (p3 ∧ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149181738941651561128806739809 : (((False → p5) ∧ ((((((p3 ∨ (p2 → p2)) ∨ (p5 ∨ p2)) → (p5 ∧ (p1 ∧ p1))) ∨ True) ∨ p2) ∨ p3)) ∨ (p2 ∧ (True ∨ (False ∧ p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117357043798059538411560409610 : ((False ∧ (p5 ∧ (p1 ∧ (((p3 → (p4 ∧ (p2 ∨ p4))) ∧ ((p4 → (False ∨ ((False ∧ (p1 ∨ p3)) → p2))) → p5)) ∨ True)))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586521127110137967001039610258 : ((((((True ∧ True) ∧ ((((((False ∨ (((False ∧ p4) → p1) ∨ p5)) ∨ p4) ∨ False) ∧ True) ∧ p1) ∧ (p2 → (False ∨ p3)))) ∧ p5) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61556387014832638980919287707 : ((p1 ∧ ((((True ∨ False) ∧ p4) ∧ (p4 ∧ (p4 ∨ False))) ∨ (((p3 ∧ (p4 → ((((p2 → p1) ∨ True) ∧ p5) → p1))) ∨ p2) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57876748455117312724646505932 : (((p1 ∨ (p1 → p4)) → ((p5 → (p4 → ((p1 → p3) ∧ (False ∨ p2)))) ∨ ((False → False) ∨ (p1 ∧ (((True ∧ p5) ∨ p3) ∨ p2))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672150732473727589911541837719 : (((((p2 ∧ (((((p1 → (False → p3)) ∨ (False ∨ ((p5 ∧ p2) ∨ p3))) ∨ p1) ∧ (True → p3)) ∧ p4)) ∨ p2) → ((False ∨ p2) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348200965440140940797244058488 : (p3 → ((False → True) → ((p1 → (False ∧ p5)) ∨ (False ∨ ((((((((p2 → p5) ∨ True) → p3) ∧ p4) ∨ False) → True) ∧ False) ∨ (True ∨ p3)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234095362062450453413225772680 : ((True → (p4 ∧ p3)) → (p5 → ((((((p2 ∨ ((p3 ∨ (p5 ∧ (True ∧ False))) → p2)) ∨ (p2 → p1)) → p2) ∧ p2) ∨ (p5 ∧ p1)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172120677202229724909505431166 : ((((((p4 ∧ (p5 → (p3 → p4))) → p3) → False) → False) ∧ ((p3 → True) ∧ p3)) ∨ ((p1 ∨ p3) ∨ ((p1 ∨ p3) ∨ (False → (False → p5))))) := by
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
theorem thm_5_vars_68822007335309161968019867664 : ((p4 → ((p1 ∧ (False ∨ p2)) ∨ (((((((False → p4) ∧ p2) ∧ p5) ∨ False) ∨ (True ∨ True)) ∨ ((p4 → (False → p5)) ∧ p3)) ∨ p5))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136388135138876897183585757015 : ((((p4 → p1) → (False ∨ p5)) ∨ ((((p2 ∨ (p4 → (False ∨ p1))) ∧ p4) ∧ (p5 ∨ p5)) ∧ (p4 → (p5 → p5)))) ∨ (True ∨ (p3 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152672077653982380455790727090 : (((p5 → True) ∧ ((p2 → (p1 ∧ ((((p1 ∨ p4) → p3) ∨ p1) → (p5 ∧ True)))) ∨ (p4 → (p4 → p1)))) → (p5 ∨ (p1 ∨ (False → p2)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800475877483772135202830113813 : (((p2 → ((((((p2 ∨ (p2 → p3)) ∨ p3) ∨ p2) ∧ (True ∨ (((p4 ∧ (p1 → True)) → False) ∨ (p2 ∧ (p1 → p2))))) ∧ p5) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49189446437287565940390358000 : (((((False ∨ p5) ∧ False) ∧ (p3 ∨ (p3 ∧ ((False ∧ p4) → (p4 ∨ (p4 ∧ (((p5 → False) ∨ p4) ∧ False))))))) ∨ ((p2 ∨ p2) → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117046299931851524249143275195 : (((p4 ∨ False) → ((((((True ∨ True) → (p3 ∧ (p4 → True))) ∨ True) ∧ ((True → True) ∧ p4)) → p2) ∨ (p1 ∨ (True ∧ p4)))) ∨ (True → p5)) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231315218239784243795938552175 : (((True → False) ∨ p1) → ((((((((p1 ∨ p3) → (p3 ∧ p5)) → (p4 → False)) → p4) ∧ ((False → p1) ∨ True)) → (True → False)) ∧ p4) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51501440127640778492475895371 : (((((p3 → p1) ∧ p4) ∨ (False → (False ∨ ((((True → p1) ∧ False) → (False ∨ True)) → p4)))) → (p2 ∨ (True ∧ (p2 ∧ (p5 ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54073303502533403059085460563 : ((((p1 ∨ (False → True)) → ((p5 → (p2 ∨ True)) ∨ p4)) → ((p4 → p1) ∨ (p3 ∧ (p1 ∧ ((p2 → ((p1 ∧ p1) ∨ p2)) → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643433128387665855099441584486 : ((((p4 ∧ ((((p2 → p2) ∨ (p4 → p1)) ∧ ((p4 ∧ ((p5 ∨ p1) ∧ (p3 ∧ (False ∨ p5)))) ∧ ((p2 → p4) ∧ p3))) → p2)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769162919605938501315273105966 : (((p5 ∧ ((p3 → p1) ∧ ((((p1 ∨ (p1 ∨ p4)) ∨ (((p2 ∨ p1) ∧ ((False ∧ ((False ∨ p5) → p1)) → p5)) → p5)) ∧ p5) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620620198595431151157684758457 : (((((True ∧ True) → (((True ∨ p4) → ((p3 ∧ (((p1 ∧ (p5 → (p5 → (p1 → p4)))) ∧ (False ∨ p2)) → False)) → False)) → p1)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_41616901959339455755142746462 : ((((p5 → ((p5 → (p2 ∨ p4)) ∧ (p1 ∨ p1))) ∨ ((((p5 → (p4 ∨ p5)) ∨ p3) ∧ ((p3 → (p4 ∨ p2)) ∧ p5)) ∨ p5)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712634601197738101372488002172 : (((((False ∧ p1) ∧ (p3 ∧ (p3 ∨ p1))) ∨ (((True → ((True ∧ p3) ∨ p4)) ∧ (p1 ∧ (p4 ∧ ((p2 → (False ∧ p3)) ∨ False)))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797213187224163107698676992126 : (((p1 → ((((p5 ∨ ((((p3 ∨ p4) → p4) → p4) ∨ (p1 ∨ ((p2 → p5) → ((True ∧ p3) ∧ (p4 ∨ True)))))) ∧ p4) ∧ p5) ∨ p1)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136716103227547528647897847787 : (((p3 ∧ p2) ∧ (((p3 ∨ (((False ∧ ((True → (False → p3)) ∨ (p5 ∨ p2))) ∧ (p4 ∨ p5)) ∧ p1)) ∨ False) ∨ p2)) ∨ ((True → p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187351034091609391833546177147 : ((p2 ∧ (False → (p4 → (((p4 → False) ∧ True) → (p5 ∧ p3))))) → ((p5 ∧ (((False ∨ (False → p2)) ∨ p3) → (p2 → (False ∧ p5)))) → False)) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : ((False ∨ (False → p2)) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h7
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45473610875420133801943712346 : (((False ∨ ((((p2 → p1) → ((((p1 → p4) ∧ (p3 ∨ p3)) ∨ ((p5 ∨ p5) ∨ p1)) ∨ (False ∧ p4))) ∧ p1) ∨ (p3 → p3))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227828254414077791058902086665 : ((p2 ∧ (p3 ∧ False)) ∨ ((((True ∧ (p4 ∨ (p1 ∧ (((False ∨ ((p5 → p5) ∨ True)) ∨ False) ∧ (True ∧ p2))))) → p4) → p5) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309820357853692836738734832123 : (p2 ∨ ((p1 → (((True ∧ ((p2 → (False ∧ p5)) → p2)) ∧ ((True → True) ∧ (p4 → (p2 ∨ p1)))) ∧ p2)) ∨ (True ∨ ((p1 ∧ p4) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318883109221513880182372497404 : (p4 ∨ ((((p2 ∧ True) ∨ p4) ∧ ((p1 ∧ ((((p1 ∨ p3) → False) ∧ p5) → ((True ∧ (p5 → False)) ∧ True))) → False)) ∨ ((p4 → p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219769851767930059558907903265 : ((p2 → ((p1 ∧ p1) → p4)) → ((((p3 → p3) ∨ (False ∧ ((p1 ∧ (True ∨ p3)) ∨ ((p5 → False) → p5)))) ∧ ((p1 → True) → False)) → p5)) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (p1 → True) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h6
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230061633212644285488090067258 : (((p2 ∧ p1) ∧ p1) → ((((p2 → p1) ∧ p1) ∨ (p2 ∨ p1)) → (((p3 ∨ p1) → (False ∨ (((p3 ∧ p1) ∧ p2) → p1))) ∨ (p2 ∧ p5)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h1.left
      let h26 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h25.left
      let h28 := h25.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h29
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h31
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- Conjunctions on the left can always be decomposed.
        let h34 := h32.left
        let h35 := h32.right
        -- One of the premise coincides with the conclusion.
        exact h35
      case inr h36 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h37
        -- Conjunctions on the left can always be decomposed.
        let h38 := h37.left
        let h39 := h37.right
        -- Conjunctions on the left can always be decomposed.
        let h40 := h38.left
        let h41 := h38.right
        -- One of the premise coincides with the conclusion.
        exact h41
    case inr h42 =>
      -- Conjunctions on the left can always be decomposed.
      let h43 := h1.left
      let h44 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h45 := h43.left
      let h46 := h43.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h47
      -- Disjunctions on the left can always be decomposed.
      cases h47
      case inl h48 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h49
        -- Conjunctions on the left can always be decomposed.
        let h50 := h49.left
        let h51 := h49.right
        -- Conjunctions on the left can always be decomposed.
        let h52 := h50.left
        let h53 := h50.right
        -- One of the premise coincides with the conclusion.
        exact h53
      case inr h54 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h55
        -- Conjunctions on the left can always be decomposed.
        let h56 := h55.left
        let h57 := h55.right
        -- Conjunctions on the left can always be decomposed.
        let h58 := h56.left
        let h59 := h56.right
        -- One of the premise coincides with the conclusion.
        exact h59



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147344775604589804717794291867 : (((((p3 → (False ∨ p3)) ∨ (((p1 ∧ False) → p1) ∧ ((p1 ∨ (p4 → p2)) → p4))) → (p3 ∧ p4)) ∨ True) ∨ ((p1 → (p2 → p1)) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_914661218279235798443889797323 : (((((p4 ∧ (p4 → False)) ∧ ((p3 ∨ (((True ∨ (p1 ∨ False)) → True) ∧ p3)) ∨ p5)) ∧ (p3 ∨ (((p4 → p1) ∨ (p2 → p1)) → p2))) → p1) ∧ True) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h10 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h11 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h12 := h7 h11
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h14 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h15 := h7 h14
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h19 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h20 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h21 := h7 h20
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h23 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h24 := h7 h23
        -- False on the left can always be used.
        apply False.elim h24
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h26 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h27 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h28 := h7 h27
      -- False on the left can always be used.
      apply False.elim h28
    case inr h29 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h30 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h31 := h7 h30
      -- False on the left can always be used.
      apply False.elim h31
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3209270292464247209579983966 : ((p5 ∧ p2) ∨ (((p3 ∨ (((p5 ∧ (p5 ∧ p5)) ∨ (p1 ∨ True)) ∨ (((p5 ∨ p3) → (False ∧ True)) ∧ p1))) ∨ (p3 → True)) ∧ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140159634578586043751038564096 : (((((p1 ∨ False) ∨ (False ∧ (((((p2 → p3) ∨ True) → p3) ∧ (True ∨ p5)) ∧ p2))) ∧ (p2 → True)) → (p4 → p3)) → (p3 ∨ (False → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197119088195392265494004738883 : (((p1 ∨ (p4 → ((p3 ∨ p1) ∧ True))) ∨ p5) ∨ (p3 → (p3 ∧ ((p3 ∨ p3) ∧ ((p5 ∨ ((False ∧ p4) ∧ p2)) → ((p4 ∨ p5) ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623718487691230200491771274747 : ((((p1 ∨ (((p4 ∧ (((p1 → (p1 → p5)) ∨ p1) → ((p2 ∨ (p5 ∧ (p1 → p5))) → False))) ∧ (False ∧ p1)) ∧ (p1 → p2))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138035822767396542668357757998 : ((True → (((p3 → p2) → (p5 ∨ (p4 ∨ (p1 ∧ ((p4 ∧ p4) → (p4 → p2)))))) → ((p1 ∨ (p4 ∧ p5)) ∨ p5))) ∨ (False → (p5 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65788762922016884182974127167 : ((p4 ∨ (((((p5 ∨ (p1 ∧ p1)) ∧ (p2 ∧ True)) ∧ False) ∧ (p1 ∨ p5)) ∨ (p1 ∧ ((p1 ∨ (True → (False ∧ False))) → (False ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358096332297902396302600020038 : (p5 → (p2 ∨ ((((((p5 ∨ p5) ∧ True) ∧ p1) ∧ p1) → ((p2 ∧ ((p5 → (p3 ∨ p5)) ∧ (p5 ∨ (p4 ∨ p1)))) ∨ (p5 ∨ p2))) ∨ p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_868217056797998293356772185811 : (((((p1 ∨ False) → (False ∨ (p2 ∨ (p2 → (((p4 ∧ (p1 ∨ p4)) ∧ (p2 ∨ ((p5 ∧ p5) ∧ True))) ∨ (p4 ∨ (p4 → p4))))))) → False) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ False) → (False ∨ (p2 ∨ (p2 → (((p4 ∧ (p1 ∨ p4)) ∧ (p2 ∨ ((p5 ∧ p5) ∧ True))) ∨ (p4 ∨ (p4 → p4))))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306261758040439424904755024048 : (p1 ∨ ((True → (p2 ∧ p2)) → (((((p5 → False) ∧ p2) → ((((False ∨ (p4 ∨ ((p2 ∨ True) ∧ False))) ∨ p5) → p4) ∧ p3)) ∧ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62832515709181287028148513247 : ((p4 ∧ ((p1 ∧ ((p3 ∧ p4) ∨ (p1 ∧ (p4 ∨ True)))) ∨ (((p5 → ((p5 → p5) ∨ (p3 → (p3 ∧ True)))) ∧ (p3 → p1)) → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158244352626351739661043046148 : ((((p4 → p3) ∧ True) ∨ ((((p1 ∧ p4) ∨ ((p5 ∧ (p4 ∨ False)) ∧ p3)) → True) → (p3 → p3))) ∨ (p1 ∧ (((p1 ∧ p4) → p4) ∧ False))) := by
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
theorem thm_5_vars_646907259295283609011208272621 : ((((p2 → (p1 ∨ ((True → (False → (p1 ∨ p2))) → ((((p3 ∧ (False ∨ False)) → ((p4 ∨ p2) ∨ p4)) ∧ (p3 ∨ p1)) → p2)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607632833251084191186615768222 : (((((p4 ∧ ((((p2 → (False → ((p1 ∨ p5) ∨ p2))) ∧ ((p5 → ((p2 ∨ p2) ∨ (p4 ∧ False))) ∨ p3)) ∨ False) ∧ p5)) ∧ True) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_451457537281627039704545820438 : (((((p4 → (False ∨ (((p3 ∧ ((p1 → (False ∧ (p4 ∧ False))) ∧ p2)) ∧ p5) ∨ p2))) → (p1 ∨ p1)) ∨ (((p5 → p5) → True) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175204959555049749741028980045 : ((False ∨ ((p2 → (p3 ∧ True)) → ((((p5 ∧ False) ∧ (p2 ∧ p2)) ∧ False) ∨ p5))) → ((p5 ∧ p2) ∨ ((p3 → (False ∧ True)) ∨ (True → True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51593200226570494545914050288 : (((p1 → (p4 → (((((False ∧ p1) ∧ p4) ∨ (p5 ∧ (True → p4))) ∨ True) ∧ (p2 ∧ p1)))) → ((p3 ∨ ((p5 ∨ False) → p3)) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347372423260598362067733479654 : (p3 → ((((p5 → (p4 ∨ (p1 ∨ True))) ∨ p2) → p2) ∨ (True ∨ (p2 ∧ (p2 ∨ (p2 ∧ (p3 ∧ ((p2 ∨ p4) ∧ (p1 ∧ (p4 ∧ p4)))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113628243079207188112386538649 : (((p2 → ((p5 ∧ p1) → ((((True → (p4 → (p4 → ((p3 ∨ p3) ∧ False)))) → (p4 ∧ p1)) ∨ True) ∧ True))) ∨ (p2 ∧ False)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306569087808890260248273638371 : (p1 ∨ ((p2 ∨ p4) → ((p3 → (p2 → ((((p3 ∧ (True ∧ False)) ∨ ((((True ∧ p3) ∧ True) ∧ False) ∨ p3)) ∨ p5) ∨ (p4 ∧ p3)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_313178262375693019578877115050 : (p3 ∨ (((((((p1 → True) → p2) ∧ False) → p2) ∧ p5) → (((p5 ∧ True) ∧ (p5 ∨ (p1 → (p5 → ((False ∧ p2) ∨ p2))))) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747562282578124621954983405804 : ((((True → p3) → ((p2 ∧ (((True → True) ∨ p1) ∧ (True ∧ (p3 ∧ (((p3 ∨ (p2 → p4)) ∨ p2) → ((True ∨ p3) ∧ False)))))) → p4)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : ((p3 ∨ (p2 → p4)) ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h6.left
    let h17 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
    have h20 : ((p3 ∨ (p2 → p4)) ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h19, we can now drive its conclusion.
    let h21 := h19 h20
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- False on the left can always be used.
    apply False.elim h22
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356566139576619915003062622124 : (p5 → (((p2 → p1) ∧ (p5 ∨ ((False → True) → (p4 → False)))) → ((p4 → ((p4 ∧ p2) ∧ (False → (True → (p3 → p2))))) ∨ (p4 ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65624882554546323463923258494 : ((p4 ∨ (((((True ∧ True) ∧ (((((False ∧ False) ∨ (p2 ∨ p4)) ∧ p4) ∨ (p5 → (False → (True ∨ p4)))) ∨ p2)) ∨ p3) ∨ p4) ∨ p5)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_246690465469637854984173506519 : ((p5 ∧ p4) ∨ (((((p4 ∧ (p5 ∨ False)) → ((False ∨ (p2 ∧ True)) ∧ (False ∨ (p5 → p1)))) ∨ p2) → ((p2 → False) ∨ False)) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203858544190364226258679738594 : ((False → (p2 ∨ ((p3 ∨ p1) → p4))) ∧ (p5 → ((p4 → (p5 ∧ True)) → ((False ∨ (p5 ∧ (p3 ∧ ((p2 ∨ p1) ∨ False)))) ∨ (True ∧ p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47647286916841087667208262700 : (((((p3 ∨ (True → (False ∧ (False ∨ (p2 ∧ ((p3 ∧ p1) → (p5 ∧ (False ∨ (p2 ∧ (False ∨ p3)))))))))) → p2) ∧ p5) → (p4 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175516040313190905924623312404 : ((p3 → (p4 → ((p2 ∧ ((False → (((p1 → True) → False) → p2)) ∨ True)) ∨ p5))) → ((((False ∧ p4) → p3) → (False ∧ p2)) ∨ (False → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67397714799023121901288404455 : ((p1 → ((p2 → (((p2 ∧ ((((p3 ∧ True) → (True ∨ True)) → ((p5 → p4) → (p4 ∧ False))) ∧ p3)) ∧ (p2 → p2)) ∧ False)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314619317067853662791307649310 : (p3 ∨ (((((p4 ∨ p2) ∨ p2) → ((True ∨ p5) → (p4 → p1))) → (True → (True ∨ True))) ∧ (False ∨ ((p5 ∧ (p4 ∨ True)) ∨ (p5 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40500791311439290658932956847 : ((((False ∧ ((((((p1 ∧ True) ∧ (True ∨ p5)) ∧ p3) ∧ p5) → ((p3 → p4) ∨ p2)) ∧ ((p3 ∧ False) ∨ (p4 → p1)))) ∨ True) ∨ p2) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149613882351424311696466034828 : ((p3 ∧ (p2 ∧ ((((p1 ∨ True) ∧ (p5 → p2)) ∨ ((False ∧ p3) ∧ False)) ∨ ((p4 ∧ p2) → (p4 → False))))) ∨ (p2 ∨ (p5 → (p2 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53845034089880792003913176102 : ((((((p1 ∧ p3) ∨ p2) → p3) → (False ∨ (p3 ∨ False))) ∨ ((p2 ∧ (True ∨ (p3 → p5))) ∨ ((p2 → p2) ∨ ((p4 ∨ p3) → p2)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



