variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39837306491501217592860866193 : (((p1 → (((True → (((False ∨ p3) → (((((p2 ∧ p5) ∧ True) → p2) ∨ p4) ∨ p4)) → p2)) → (p5 ∧ p1)) ∨ (p1 ∨ True))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42414614503788795518960977147 : (((p5 ∧ (((p2 ∧ ((p1 ∨ (p5 ∨ (((False ∧ p4) ∨ p2) ∨ p1))) ∨ (p5 ∧ (((False ∧ p5) → p1) ∨ p1)))) ∧ p1) → p4)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68544944433228301612959580223 : ((p3 → (p3 → (p1 ∨ ((p3 → p2) → ((((p5 → (p1 → True)) ∧ False) ∧ ((((False ∨ False) → (p2 ∨ p2)) → p4) → p2)) ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343300051017166405771282217176 : (p2 → ((True ∨ p3) ∧ ((p4 → p2) → ((p3 → (p4 ∨ ((True ∨ (((p5 ∧ (p1 → p4)) ∨ (True → False)) ∧ p2)) ∧ p4))) ∨ (True ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124063531983024982653489090197 : ((((p1 ∧ p5) ∨ (True ∧ (p5 → (((p4 → p1) ∧ p1) → p1)))) → (((p2 → p3) ∧ (False ∨ (p1 ∧ (p1 → p4)))) ∧ p1)) → (p4 ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∧ p5) ∨ (True ∧ (p5 → (((p4 → p1) ∧ p1) → p1)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66076276845166293182452794837 : ((p5 ∨ ((p3 ∧ ((True ∧ (((True ∨ p3) ∨ (p4 ∧ True)) ∧ ((True ∨ p1) → ((True → p4) → ((p4 → True) → p5))))) ∨ p5)) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173168732638573584640530487531 : ((p4 ∨ (((False → ((False ∨ (p5 ∧ p2)) ∧ (True ∧ p2))) → (p1 → p5)) ∨ True)) ∨ (((False → True) ∧ p4) ∨ (p1 → ((p2 ∧ p2) ∧ True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179376281859482591535933062020 : ((p2 ∨ (p4 ∨ (p4 ∧ (p3 ∧ ((False → False) → ((False ∨ False) ∧ False)))))) ∨ (((p1 → (False → (p1 ∧ p1))) ∧ (False → p1)) ∨ (True → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172610137893189356953804542275 : (((False → (p4 ∧ True)) → ((p5 ∨ (p3 ∧ (p5 ∧ (p2 ∧ p5)))) → (False ∨ p3))) ∨ (p5 ∨ ((((p2 ∧ p5) ∧ p1) ∨ p4) → (True ∨ True)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121670616888748875696946449019 : (((((p1 ∨ p1) ∧ ((p5 → ((True ∧ False) ∧ p4)) ∧ (p1 → p4))) ∨ ((False ∧ (p1 ∨ p5)) → ((True → p1) → p1))) → p5) → (p5 ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ p1) ∧ ((p5 → ((True ∧ False) ∧ p4)) ∧ (p1 → p4))) ∨ ((False ∧ (p1 ∨ p5)) → ((True → p1) → p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65829013024605960668051621654 : ((p4 ∨ ((((False → p4) ∨ p3) → p4) ∨ (p5 ∧ ((True ∧ (p4 → (False ∧ (((True ∨ p2) ∨ (p1 ∧ True)) → True)))) → (True → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157389372121127475618916312435 : ((((p2 ∧ (((p5 ∨ (p3 ∧ True)) ∧ p1) ∨ (p4 ∨ (p2 → (p3 ∨ p5))))) ∨ False) ∧ (p2 → True)) ∨ (True ∨ (p5 ∨ ((False ∨ p5) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62088898657343430842901415750 : ((p2 ∧ (p3 ∧ (True ∧ ((p1 → ((p1 ∧ p4) ∧ (False ∧ (p2 ∨ ((p4 ∧ p4) → (((p4 → p3) ∧ p4) → True)))))) ∧ (False ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114405323053272666949047302400 : (((((p2 → (p1 ∧ p2)) → (False ∧ p1)) → (p2 ∧ (False ∨ (p4 → ((p5 ∨ p4) ∧ p5))))) ∨ ((p1 → p2) → (p5 → p5))) ∨ (False ∨ p2)) := by
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
theorem thm_5_vars_41652698018704674039452186068 : (((((p4 ∨ True) ∧ ((False ∧ p1) ∧ p5)) ∧ ((((p4 ∧ (True ∨ True)) → False) ∨ p5) ∧ ((p3 ∧ (p2 ∧ p3)) → (True → p3)))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744664486268755469302781898730 : ((((p3 ∧ True) → ((True → (p4 → True)) → ((((p1 ∧ (p5 ∨ p1)) → ((p5 ∧ (p4 ∨ True)) ∧ p2)) ∨ p3) ∨ ((p3 ∧ p3) ∨ p3)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110790386544905133918354267566 : ((((((((p4 ∧ p4) ∨ (p2 ∧ p4)) ∧ ((p2 ∧ p3) → ((p5 ∧ p1) ∨ p3))) ∨ ((False ∨ False) → p4)) → False) ∨ p2) ∧ False) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117163895787026860330609902869 : ((True ∧ ((p3 ∨ (((p3 ∧ ((p2 ∨ (True ∧ p4)) → True)) ∨ ((False → True) → (((True ∧ p4) → p4) ∧ p3))) ∨ True)) ∨ p3)) ∨ (p3 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113582911053903981489201773874 : (((p2 ∧ ((((False ∧ (True ∨ (p1 ∨ (p5 ∧ p5)))) ∨ p2) ∨ (((True ∨ (p3 ∨ False)) → False) ∧ p1)) ∨ True)) ∨ (False ∨ True)) ∨ (p4 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_577556930949489527186774293033 : (((p3 → ((((False ∧ (p5 → p1)) ∧ ((False ∧ p1) ∨ ((p4 ∧ p1) ∧ (p4 ∨ False)))) ∨ (False ∨ True)) ∧ (p1 ∨ (p3 ∨ (p3 → p5))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324633113587324373211349870355 : (p5 ∨ (((False ∧ False) ∧ p4) ∨ ((True ∧ (p1 ∧ ((p1 ∨ True) → p4))) ∨ ((p3 ∨ (False → ((p3 → p5) ∨ p2))) ∨ (p5 ∨ (True ∨ True)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71034160556207013682539298891 : ((((((p3 → p5) ∧ True) ∧ (p5 ∧ p4)) ∧ (False ∨ (((((p3 ∨ p2) → (True ∧ True)) ∧ True) → ((p5 → p1) ∧ True)) → p2))) ∧ p4) → p5) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h10 := h7.left
  let h11 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h12 =>
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55687861681353658813216442842 : (((((p4 → True) ∨ p4) ∨ p4) ∧ ((p1 ∨ p3) ∧ ((p5 ∧ False) ∧ ((((True ∧ p4) ∧ p1) → (p5 ∧ p5)) ∧ ((p1 ∨ p5) → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180828381755207340932483074764 : (((p4 ∨ (p1 ∨ True)) ∧ (((False ∧ (p2 → p1)) → p2) ∧ (p1 ∧ p2))) → (((p1 ∧ p5) ∨ False) ∨ ((p2 ∧ True) ∧ ((False ∨ True) ∨ p2)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h8
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h3.left
      let h12 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h14
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h3.left
      let h17 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h19
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193101813832789268303271331871 : (((p4 ∨ ((p5 ∧ p1) ∨ True)) ∧ (True → (False ∨ p1))) → ((p1 ∧ (p4 ∧ (((p4 → (p1 ∧ p2)) ∨ p2) ∨ p4))) ∨ ((p1 → False) → p4))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h11 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h12 := h10 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h16 := h3 h15
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h19 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h18
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h20 := h14 h19
        -- False on the left can always be used.
        apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339601296513236041745049470707 : (p1 → (p2 ∨ ((((((p2 ∨ (p5 → (p5 ∧ p2))) ∧ p1) → p2) ∨ (((p3 ∨ (p1 ∨ p5)) ∨ p4) ∨ ((True ∧ True) → p5))) ∧ p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208868657437143988455213518880 : ((p4 ∧ ((p2 ∨ p3) ∧ (p1 ∨ p1))) → (p5 → (((True ∧ False) ∨ ((p4 ∧ p2) ∨ (p1 ∧ p3))) ∧ (((p5 ∧ p1) → (True → False)) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h11
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h12
      -- One of the premise coincides with the conclusion.
      exact h10
  -- Implications on the right can always be decomposed.
  intro h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h15.left
  let h17 := h15.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h19 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h20 =>
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h22 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h23 =>
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49581843735830206035735217837 : (((((True ∨ (((p5 → True) ∧ p1) ∧ p5)) → (p4 ∨ (p3 → (p2 → p5)))) → ((False ∨ (p4 → True)) → p4)) → ((True → p2) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778983971516989815023917572767 : (((p1 ∨ (p3 → ((((p2 ∨ (p4 ∧ False)) ∨ True) ∧ p4) ∧ (True → ((((False ∧ p3) ∧ (((p2 ∧ p3) ∧ p1) ∨ p3)) ∧ p2) → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322487895895044828759943889744 : (p5 ∨ (((p4 ∨ p2) ∨ (((p2 ∧ (True ∨ p4)) → p1) ∨ ((p3 ∨ (((p3 → True) ∨ (p1 → p1)) ∧ (True → p4))) ∨ (True ∨ p1)))) ∨ False)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206526331061298793635427551074 : ((True → ((p2 ∨ (p4 ∧ False)) ∧ False)) ∨ (((p2 ∧ (False → (((p4 ∨ False) ∧ p2) → (True ∧ p1)))) ∧ (False ∧ p1)) ∨ (p3 → (True ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41209785761530829958597290131 : ((((p4 → (False ∧ (((p3 ∨ (p1 ∨ True)) ∧ ((False ∧ (((p1 ∧ p1) → p4) ∧ p1)) ∧ p2)) → p1))) → ((p3 ∧ p2) ∧ p1)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174401451262690033711278925470 : ((((((p4 → p4) ∨ (False → p3)) ∨ p4) ∧ p4) ∨ (True ∨ ((True ∨ True) → p1))) → (p4 → ((False ∨ p3) → (p5 ∨ ((p5 ∧ p5) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8735918060077965224972759122 : (((((((True ∧ True) → (p4 ∧ (True → (((False ∧ p5) ∨ p5) ∨ p1)))) ∧ p4) → ((p2 → p3) → p5)) ∧ (True ∨ (p3 → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336051343819320236124699223241 : (p1 → ((p3 → (((((p5 ∧ p3) ∧ (p4 ∨ False)) → p4) → (True ∧ (False ∧ p1))) → ((p1 → (p4 ∧ ((False ∨ p2) ∧ p5))) ∧ p1))) ∧ True)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (((p5 ∧ p3) ∧ (p4 ∨ False)) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h13 := h3 h5
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- False on the left can always be used.
  apply False.elim h15
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h16 : (((p5 ∧ p3) ∧ (p4 ∨ False)) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h22 =>
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- False on the left can always be used.
      apply False.elim h23
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h24 := h3 h16
  -- We need to get the right conjuct of h24 based on <expert-advice>.
  let h25 := h24.right
  -- We need to get the left conjuct of h25 based on <expert-advice>.
  let h26 := h25.left
  -- False on the left can always be used.
  apply False.elim h26
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h27 : (((p5 ∧ p3) ∧ (p4 ∨ False)) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h28
    -- Conjunctions on the left can always be decomposed.
    let h29 := h28.left
    let h30 := h28.right
    -- Conjunctions on the left can always be decomposed.
    let h31 := h29.left
    let h32 := h29.right
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h33 =>
      -- One of the premise coincides with the conclusion.
      exact h33
    case inr h34 =>
      -- False on the left can always be used.
      apply False.elim h34
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h35 := h3 h27
  -- We need to get the right conjuct of h35 based on <expert-advice>.
  let h36 := h35.right
  -- We need to get the left conjuct of h36 based on <expert-advice>.
  let h37 := h36.left
  -- False on the left can always be used.
  apply False.elim h37
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64290680603804981341417053141 : ((False ∨ (p3 → ((((p5 ∧ ((False ∨ False) → (((False ∧ p5) ∨ ((p5 ∧ False) ∨ (p4 ∧ p5))) ∨ p4))) ∨ p2) ∨ True) ∧ (p5 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317346053956411284627183050347 : (p4 ∨ ((((((((p2 ∧ p5) ∨ (p2 → (p5 ∧ p3))) → p5) ∧ p1) ∨ p2) → p2) ∨ ((((p2 ∧ p4) → p1) ∧ (p5 ∨ p4)) ∨ True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_48963692309316239980576152573 : ((((((((((p5 → p4) ∧ p4) → (p3 ∧ True)) ∧ (((p3 ∨ p1) ∧ p4) ∨ p3)) ∨ p2) ∧ p3) ∨ p3) ∨ True) ∨ (False → (False ∧ False))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168839042379191632709180200407 : ((p3 ∨ (((((p2 → p1) ∧ (False ∨ p3)) → (p3 ∧ False)) ∧ p2) → ((p4 → p4) ∧ p1))) → ((True ∧ p1) ∨ (False → ((p2 ∨ p3) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339164929435940061524903717285 : (p1 → (p1 ∧ (True → ((((p2 ∧ p1) ∨ (False ∧ ((False → (p5 ∨ (p2 → p1))) ∨ p3))) ∧ (False ∨ (p4 ∧ (p4 ∨ p1)))) ∨ (p3 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40361542160667873168388840755 : (((((((True ∧ (p2 ∨ ((True → p3) ∨ p2))) ∨ p1) ∧ (((p2 → (p3 → False)) ∧ ((False ∨ p2) → False)) ∨ p5)) → p2) ∨ p4) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247408998816384608510516116054 : ((False ∨ p2) ∨ (((p2 → (p5 ∧ (p1 → p3))) ∧ ((p5 ∨ (False ∧ p4)) → ((((p5 → False) ∧ p4) ∨ (p4 ∨ (True → True))) → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327838939084821925917466494884 : (True → (((True ∧ (((True → (p5 ∧ False)) ∨ ((False ∨ p1) → p2)) ∧ ((p5 ∨ False) → p1))) → ((p1 → False) ∧ (p3 ∨ p3))) ∨ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133627952467176933528855349362 : (((((True → p2) → ((p5 ∧ (p5 ∨ (p1 ∨ False))) ∨ (((p4 ∧ p5) ∨ p2) ∧ (True ∨ (p3 ∧ p5))))) → p3) ∧ p5) ∨ ((p3 ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117017855413643813452833091423 : (((p1 ∨ p3) → ((((p3 → p5) → (((((False ∧ (p1 ∨ (True ∧ p5))) ∨ False) ∨ p3) ∧ p3) → p5)) → p4) ∨ (True → p1))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187737984773377985329059684394 : ((p1 → (p1 ∨ (((p4 ∧ (True ∨ False)) ∨ (p3 ∧ p5)) ∨ p5))) → ((((((p2 → p4) ∧ False) → p5) → False) → p3) ∧ (p2 ∨ (p1 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p2 → p4) ∧ False) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h3
  -- False on the left can always be used.
  apply False.elim h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118854156696488727742962487294 : ((True → ((p5 → (((p4 → p5) ∧ (p3 ∧ ((False ∧ False) ∨ p4))) ∧ p4)) → (((p3 ∧ (p4 → (p4 ∧ True))) ∧ False) ∨ p2))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164692677573000813295420206368 : ((((((p4 ∧ (((p4 ∨ p2) ∨ (p5 ∧ (p1 ∧ p4))) → True)) ∨ p3) ∨ p4) ∨ p1) ∨ p3) ∨ (True ∨ (((p4 ∧ (p1 ∨ p5)) → p1) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319639244861078417462526742022 : (p4 ∨ (((p4 ∨ ((False ∧ p1) ∧ p1)) ∨ (False → p3)) ∨ (p4 → ((((True → False) → (((p2 ∨ False) ∨ True) ∧ (False ∨ False))) → p2) ∧ p3)))) := by
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
theorem thm_5_vars_65119295980599311266771356387 : ((p2 ∨ (True → ((((p4 ∨ p3) ∧ (p4 ∧ p3)) ∧ ((p5 ∧ ((p4 → p5) ∨ p2)) ∨ p1)) ∧ (p1 → (((p3 ∨ True) ∧ p5) ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40041205750680620849708182600 : (((((p2 ∧ (((p5 → (p4 → ((((p2 → (True → (p4 ∨ p3))) ∨ p5) → (True ∨ p4)) ∨ p3))) → p5) ∨ p4)) ∧ p4) ∧ p2) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781870070202055899255745001 : (((p4 → p2) ∨ ((True ∧ (True ∨ (p1 → False))) ∧ (False ∧ ((((p3 → (p5 ∧ p5)) ∨ (p4 ∨ p1)) ∧ p4) ∧ (p4 ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43857115280044975553340054044 : ((((((p4 → p5) ∧ (p2 ∧ ((p4 ∨ (True ∧ ((p1 → p4) ∨ p3))) ∨ True))) ∨ ((p1 ∨ (p3 → p5)) → p5)) ∧ (p3 → p3)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172330208574977640065313111144 : ((((p1 → ((False ∧ False) ∨ True)) → p5) ∧ ((((p3 ∧ p3) → p1) → p5) ∨ p2)) ∨ (p1 ∨ ((p1 ∨ ((True → False) → (p5 ∨ p3))) ∨ p5))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675918506352355222641611746372 : (((((((False ∨ (False ∧ (True ∨ p5))) ∨ (p1 → p3)) ∧ True) ∨ (((p2 ∨ p5) → (False ∧ True)) → p1)) ∧ (p4 → ((p5 → p1) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309333315026694771217254251093 : (p2 ∨ ((((p1 ∧ ((False → (p5 → False)) → True)) ∧ (((p4 ∨ (p4 ∧ p2)) ∧ (p2 → p3)) ∨ (p1 ∨ p2))) ∨ (p1 → p5)) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134993110058294130253487517085 : (((True ∧ ((p3 ∨ (p4 → (p4 ∨ False))) → ((((p1 → p2) → ((True ∨ p2) ∨ p5)) ∧ p1) ∨ p2))) ∧ (True → p3)) ∨ (False → (p3 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671228156114930183351439445672 : ((((p4 ∨ ((((p5 ∨ ((p1 ∨ (p4 → (p5 ∧ (True ∧ p1)))) ∨ False)) → False) ∧ ((True ∨ True) → True)) ∨ True)) ∨ ((p3 ∨ p4) → True)) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207012338139733220364067694486 : ((((p2 ∨ p2) ∨ (p5 → p5)) ∧ True) → (p3 → (((((p4 → (p2 ∧ p2)) ∨ ((p2 ∨ (True ∧ (True ∨ p3))) ∨ True)) ∨ p2) ∨ p2) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
theorem thm_5_vars_147754219928444591433608576157 : ((((p4 ∧ (p5 ∧ False)) ∨ (p1 → ((((True ∨ False) → p5) → (p2 ∧ (p5 ∨ (p4 ∨ False)))) → False))) → p3) ∨ ((p1 ∨ True) → (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180657631762103018548605696214 : (((p3 ∨ (True → (p4 ∨ (False → p5)))) ∨ ((p3 ∧ p3) ∧ (p2 → False))) → ((True ∧ ((p1 → p3) ∨ p2)) ∨ (((p3 ∧ p5) → p1) → True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598830766264863960369920314286 : (((((p3 ∧ p4) ∧ ((p1 ∨ (((((True → (p5 ∧ ((True ∧ p5) → False))) ∧ p3) ∧ False) ∧ (p1 → p3)) ∧ (p2 → p4))) ∨ True)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52141681200200296211554660760 : ((((True → ((((p4 ∨ p2) ∨ True) ∧ p1) ∧ (p4 → (p3 ∨ p3)))) ∨ (p1 ∨ p1)) → ((p1 → p5) → (p2 ∨ (p4 → (p1 ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256931754017920177414601665457 : ((p1 ∨ p4) → (p2 → (((p4 → (((p1 → (False ∧ (p2 ∧ p3))) ∧ (p4 ∨ (p1 ∨ p2))) ∨ (False ∨ p3))) → (p4 → False)) ∨ (p5 ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121373275206635115363265294175 : (((((True ∧ (p1 → (((p1 ∧ p2) ∨ (p1 → ((((p1 ∨ p5) ∨ p4) ∨ p4) ∧ (p1 → p1)))) ∧ p4))) → p2) ∨ True) → False) → (p4 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((True ∧ (p1 → (((p1 ∧ p2) ∨ (p1 → ((((p1 ∨ p5) ∨ p4) ∨ p4) ∧ (p1 → p1)))) ∧ p4))) → p2) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37734687820198832811443744187 : ((((((p1 ∨ (p4 ∨ (p1 → True))) ∨ ((False → p1) ∧ p2)) ∨ (((p2 ∨ ((p1 ∨ (p5 ∨ p4)) ∧ p3)) → p1) ∨ True)) → p5) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230430319762902165363792491428 : (((p4 ∨ p3) ∧ p5) → ((((True ∧ (p5 ∧ False)) ∧ (p3 ∨ p3)) ∨ False) ∨ (p3 → (p1 ∨ (p3 ∨ (((False → (False → True)) ∨ True) ∨ p5)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115409439089706677597007743683 : (((False → ((p1 → (p2 ∨ p5)) ∨ (False ∨ p4))) ∧ (((True ∧ p5) ∧ (p3 ∧ (((p5 ∨ (True ∨ p3)) → True) → p4))) ∧ p1)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61126613060551180315938334465 : ((False ∧ ((p5 → ((((p1 ∨ p3) ∨ p3) ∧ (p1 ∧ True)) ∨ p2)) → ((p3 ∧ ((p3 → p3) → ((p4 ∨ (p2 ∧ True)) ∨ p2))) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119589134956345855877416788628 : ((p5 → ((True → p4) → (p4 → (False ∨ ((((False → (True ∨ True)) → p1) → p2) ∨ (p3 ∨ ((False ∨ p2) → (p4 ∨ p4)))))))) ∨ (p2 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56063986904573214952016235868 : (((((p5 ∨ p5) → p2) → p4) ∨ (((p2 ∨ False) ∨ False) ∨ ((p1 ∧ ((p4 ∧ False) ∧ p5)) → (((p4 → p5) ∧ p5) → (p3 → False))))) ∨ p4) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731632489299226731957542286863 : ((((p1 → (True → p2)) → (p1 ∧ (((((False ∨ (p1 ∨ True)) ∧ ((p4 ∨ (p1 → p1)) ∨ p4)) ∧ True) ∧ ((p3 ∧ True) → p4)) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232724782179088911324243802421 : ((p1 ∧ (p5 ∨ p5)) → (p5 ∧ (((True → True) → (p4 ∨ (p3 → p4))) ∨ ((p5 ∨ (p1 ∨ p5)) ∨ (True ∧ ((p1 ∨ (p4 ∧ True)) → p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126051032050854881214547845930 : (((p4 → False) → ((True ∧ ((False ∧ p4) → p4)) → (True ∨ (((((p4 → p2) ∨ False) → p1) → p2) → (p5 ∨ (p1 → p3)))))) → (p2 → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314667416354470669744899939168 : (p3 ∨ ((True → ((False ∧ p1) ∧ (True → ((p5 ∧ (p1 ∨ ((True → p1) ∨ True))) ∨ p5)))) ∨ (p5 → ((p2 ∨ p4) ∨ ((p5 → True) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_609356150760626419431756162289 : ((((((p2 ∨ p2) ∨ ((((p3 ∧ True) ∧ ((p4 ∧ (p3 → p1)) → (p5 → (p4 ∧ ((p4 ∧ False) ∧ p5))))) ∧ False) ∧ False)) ∨ p4) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1650830622242771137001610676 : (((True → False) ∧ (True ∨ ((p2 ∨ p4) ∧ (((p4 ∧ True) ∧ p4) → ((p3 → False) ∨ (((False ∧ p3) → False) ∨ False)))))) → (p3 ∨ p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
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
theorem thm_5_vars_60918688460077939880388269340 : ((False ∧ ((((((((p3 → (True ∨ False)) → True) ∨ p4) → p2) ∨ False) → (((False ∨ p4) ∨ (p5 → p2)) ∨ p4)) → (p1 ∨ p5)) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173127892409552687689390021544 : ((p2 ∨ (p4 ∧ (((p2 ∧ p2) → p4) ∧ (p3 → (p2 ∨ (p4 ∧ (p4 ∨ p3))))))) ∨ ((p1 ∨ (((True → True) → False) → (p3 ∧ False))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (True → True) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110872370574718907978848360434 : ((((((((((False ∧ p4) ∧ (True → ((p1 → (True ∨ p5)) ∧ p3))) ∧ p1) ∨ p3) ∨ False) → p2) ∧ (p4 ∧ True)) → False) ∧ False) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193420822690855382177537294997 : (((p2 ∨ p5) ∧ ((p4 ∧ p2) → ((p5 ∧ p1) ∧ True))) → ((p1 ∨ ((p4 ∧ (p1 ∨ (True ∧ (p2 ∨ ((p5 ∨ False) ∧ True))))) → p2)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h16 =>
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h17 =>
          -- False on the left can always be used.
          apply False.elim h17
  case inr h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54397193986793041749222930049 : (((((((p1 ∧ p3) → p2) ∧ p2) → p3) ∧ p3) ∨ (p4 → (((p4 ∧ True) → True) ∨ (p5 ∨ (p5 ∨ (p5 ∨ ((p3 → p3) ∨ p5))))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307483490972805874602950792809 : (p1 ∨ (True → ((((p1 ∧ False) ∨ ((((((p4 → False) ∧ ((p4 ∨ p4) ∧ p4)) ∨ p3) → p1) ∧ (p2 → p1)) ∧ (p4 ∨ False))) ∨ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726035167702091620008313843144 : (((((True ∧ p1) ∨ p5) ∨ ((p2 ∧ (p3 ∨ p3)) ∨ (p2 ∨ (p5 → (((((p2 ∧ p3) ∨ (p5 ∨ p4)) ∧ True) ∧ p5) → (True → p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127690696684080469671819411278 : ((p5 ∨ ((p5 → p5) → ((((p1 ∧ p3) → ((p2 → (p2 ∧ p5)) → p3)) ∨ (p5 ∧ ((p5 ∨ p2) → p3))) ∧ (p5 ∨ False)))) → (p5 ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p5 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184701564389631441487526541493 : ((((p1 ∧ ((False → p2) → p4)) → p3) → ((p5 ∧ p4) ∨ p4)) ∨ ((((p2 ∧ (((p5 ∨ p2) ∨ p1) ∨ (p3 ∧ p2))) → p1) → True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667904301775646683721442736939 : ((((p2 ∨ ((((p4 ∨ (p2 → p3)) → (((p1 ∨ p3) ∧ p5) ∨ ((p5 → (p1 ∧ True)) ∧ False))) → p2) → p5)) ∧ (False → (p3 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159029022279249561915694340794 : ((p4 ∨ (True ∧ (((p1 ∧ p2) → ((p2 → ((p4 ∨ False) ∧ False)) → p4)) ∧ (True → (p4 → p2))))) ∨ (True ∧ (p2 → ((p1 ∧ False) ∨ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53926797742700386557899933892 : (((p4 ∨ ((p2 → (True → p4)) ∨ ((p1 → p3) ∨ p2))) ∨ (p3 ∧ (p2 ∧ ((p4 ∧ ((False → p1) ∧ (p2 ∨ p2))) ∧ (False ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200793405339872529325390813649 : ((p4 ∧ (p5 → ((True ∨ p4) ∨ (p5 → False)))) → (((p5 → ((False → (p1 → (((False ∧ p1) → (p5 → p2)) → p5))) ∧ p5)) → False) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (p5 → ((False → (p1 → (((False ∧ p1) → (p5 → p2)) → p5))) ∧ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h7
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h5
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321375916979552519511410719073 : (p4 ∨ (True → (((False ∨ p1) ∨ (p5 ∨ (p5 ∧ (p4 → (False → (p3 ∧ p2)))))) ∨ (False → ((p2 → p1) → ((p1 ∧ p5) → (False ∨ p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653594729723593301904327706933 : (((((((p1 ∨ p1) ∧ (p5 ∨ (p1 ∨ ((p1 ∨ (p3 ∧ (((p5 → False) → False) → p5))) → (p2 ∨ p2))))) ∧ p4) ∧ p5) ∨ (p4 → True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_729029025097265449180826025509 : (((((p3 ∨ p4) ∧ p5) → ((((p3 ∨ ((p3 ∧ p2) ∨ (False → p1))) ∧ (True → (((True ∧ (p3 ∧ p5)) ∨ False) ∨ p5))) ∨ p3) ∨ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136543142569106462355356150968 : ((((True ∨ True) ∧ p5) ∨ ((p1 ∨ p1) ∧ ((((((p4 → p5) ∧ p2) ∨ (p1 ∨ (p4 ∨ p1))) ∨ p1) ∧ p2) ∨ p4))) ∨ ((p2 ∨ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729461345069580259390092796832 : (((((True ∨ p3) ∨ p2) → (p1 ∨ (p1 ∨ ((((p1 → p3) → (p3 ∧ (True → (True ∨ False)))) ∧ ((True ∨ False) ∧ p5)) ∨ (True → True))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135429562304442331579151383315 : (((p2 ∨ ((False ∨ (False → (p2 → ((p4 ∨ p3) ∧ ((p4 ∧ (p4 → p5)) ∧ p5))))) → p4)) ∨ (p4 ∨ (p4 ∧ p5))) ∨ (p2 ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_108260880459245899304377564259 : ((True ∧ ((((p3 ∧ (p4 ∧ (p4 ∧ (p1 ∨ p4)))) → (((p5 → p2) ∧ p1) ∧ p5)) → (p2 → p2)) ∨ (True ∧ (p3 ∧ False)))) ∧ (True ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139248500253444305581700144778 : ((((True → p5) ∨ (p5 ∨ ((((False ∨ p1) → ((True → ((p2 ∨ p1) ∧ True)) ∨ (True ∨ p4))) → p1) → p4))) ∨ p2) → ((p2 ∨ False) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
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
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251017043495213240545586688351 : ((p1 → p5) ∨ (((p1 ∧ p2) → ((False ∧ p2) ∧ False)) ∨ ((((p3 ∨ p5) ∧ p2) ∨ (p4 ∧ p4)) → (p2 → (p2 ∧ ((p1 ∨ True) ∨ p4)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640741231540294671746606389799 : (((((True → p2) ∧ (((True → (p3 ∧ ((p2 ∨ (False → False)) → (((((p2 ∨ p4) ∧ False) → p1) ∧ p1) ∨ p3)))) ∧ p4) → p4)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



