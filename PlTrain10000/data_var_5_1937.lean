variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123903563084076873135996147321 : ((((True → (False ∧ (False ∧ (p3 ∧ ((p5 → p5) ∨ True))))) ∧ p3) ∧ ((False → ((p2 ∨ (False ∨ p4)) ∨ (p5 ∧ True))) ∨ p4)) → (p5 ∧ p4)) := by
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
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h12 := h4 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- False on the left can always be used.
    apply False.elim h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h18 =>
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h19 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h20 := h16 h19
    -- We need to get the left conjuct of h20 based on <expert-advice>.
    let h21 := h20.left
    -- False on the left can always be used.
    apply False.elim h21
  case inr h22 =>
    -- One of the premise coincides with the conclusion.
    exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678375706421440357497294371580 : (((((((True ∨ p1) ∨ (p1 → True)) ∨ p3) → ((p3 ∨ ((((False ∧ True) ∧ True) ∧ p2) ∧ p1)) → p1)) ∨ (((p4 → p4) ∧ False) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356690939302201664427950371780 : (p5 → ((((p2 ∨ p2) ∨ p5) ∨ (True ∧ p4)) ∧ (((True → p2) → ((p5 ∧ ((((False ∨ (p4 → True)) ∧ p4) ∨ False) → False)) → False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339697878124689785182977988903 : (p1 → (p3 ∨ ((p5 ∨ p4) ∨ ((p4 → ((p4 ∨ p3) ∧ (p1 → ((((False ∨ False) ∧ False) ∨ p4) ∨ ((True → p5) ∧ p3))))) ∨ (p5 → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216606260100861143298766739748 : ((((p3 → False) ∧ p2) ∧ p1) → (p5 ∨ ((p5 ∧ (((p5 ∧ (((((False ∨ p5) ∧ p3) ∨ p1) ∧ (p5 → p2)) ∨ p5)) ∧ p2) ∨ True)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307378658831183766655307726925 : (p1 ∨ (p4 ∨ ((True ∧ (((p4 → (p5 → False)) → False) ∧ (True ∧ ((((p1 → p4) → p2) ∨ (False → p2)) → p4)))) ∨ ((True → True) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151659872000199937402762313276 : ((((p3 ∨ (((p1 → (p2 ∧ False)) → p5) ∨ p4)) → (p2 ∧ ((True ∧ False) ∧ p4))) ∧ (p1 ∨ (p5 ∧ p2))) → (False ∧ (p5 ∨ (True ∧ p3)))) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p3 ∨ (((p1 → (p2 ∧ False)) → p5) ∨ p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h8 := h6 h7
      -- We need to get the right conjuct of h8 based on <expert-advice>.
      let h9 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h5
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h17 : (p3 ∨ (((p1 → (p2 ∧ False)) → p5) ∨ p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h18
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h19 := h2 h17
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- We need to get the left conjuct of h20 based on <expert-advice>.
    let h21 := h20.left
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- False on the left can always be used.
    apply False.elim h22
  -- Conjunctions on the left can always be decomposed.
  let h23 := h1.left
  let h24 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h24
  case inl h25 =>
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h26 : (p3 ∨ (((p1 → (p2 ∧ False)) → p5) ∨ p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h27
      -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
      have h28 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h25
      -- We have shown the premise of h27, we can now drive its conclusion.
      let h29 := h27 h28
      -- We need to get the right conjuct of h29 based on <expert-advice>.
      let h30 := h29.right
      -- False on the left can always be used.
      apply False.elim h30
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h31 := h23 h26
    -- We need to get the right conjuct of h31 based on <expert-advice>.
    let h32 := h31.right
    -- We need to get the left conjuct of h32 based on <expert-advice>.
    let h33 := h32.left
    -- We need to get the right conjuct of h33 based on <expert-advice>.
    let h34 := h33.right
    -- False on the left can always be used.
    apply False.elim h34
  case inr h35 =>
    -- Conjunctions on the left can always be decomposed.
    let h36 := h35.left
    let h37 := h35.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782603241857198667447259185664 : (((p3 ∨ ((p4 → (p2 ∧ ((p5 → p4) → (((p5 ∨ (p1 ∨ ((p3 ∧ True) ∧ p1))) ∧ True) ∨ (p3 ∧ (p1 ∨ (p3 ∨ p4))))))) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_241480858198646619374440730859 : ((False → p2) ∧ (((((p3 ∧ (p1 ∧ p3)) → p2) ∨ True) → p3) ∨ ((False ∨ (((False ∧ p2) ∨ p5) → ((True ∨ (p3 → p1)) ∧ True))) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_873248492964435986627399339421 : ((((p2 → ((p2 ∧ (p1 → ((p4 ∨ (p3 → p3)) → ((p4 → (p4 ∨ ((p1 ∧ (True ∧ (p1 ∧ p3))) → True))) → False)))) ∨ True)) → False) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → ((p2 ∧ (p1 → ((p4 ∨ (p3 → p3)) → ((p4 → (p4 ∨ ((p1 ∧ (True ∧ (p1 ∧ p3))) → True))) → False)))) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168855819447397132040126399018 : ((p3 ∨ (p1 → ((p4 ∨ (p1 → ((True ∧ True) → (False ∧ p1)))) → ((False ∧ p1) ∧ True)))) → (((((False → p5) → p1) ∧ p1) ∨ p5) ∨ True)) := by
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
theorem thm_5_vars_638863485087957982233783643563 : (((((((p2 ∧ p4) ∨ True) → p1) ∧ ((True ∧ ((((True → (p5 ∨ (p5 ∧ (p1 ∧ p3)))) → p3) ∨ p3) ∨ p3)) ∧ (False → p1))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204641675388355942957821072423 : (((p1 ∧ (False ∨ (p3 ∨ p3))) ∨ p3) ∨ (p2 → ((((p2 → p1) → p5) ∨ p1) → ((p2 → (p5 ∨ False)) ∨ (True ∨ (p4 → (False ∨ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_329353940804017258841757288623 : (True → (((p4 → p2) → p5) → (True ∧ ((p2 ∨ p1) → (((p5 ∨ (True → True)) → p2) ∨ (p3 → (p2 → (((p1 ∨ p1) ∧ p5) ∧ p1)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : (p4 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h11
    -- One of the premise coincides with the conclusion.
    exact h13
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111945486495247619087006564438 : (((((((p3 ∧ p5) → (p1 ∨ p2)) ∧ True) ∧ p5) ∧ (p3 ∨ (((p5 → (((p2 → p2) ∨ p2) ∨ p1)) ∧ p5) → p5))) ∨ p3) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303224990062077422165642734856 : (False ∨ (p5 → (((p5 → (((p5 ∧ (((p1 ∨ ((p2 → p3) ∧ p2)) ∧ (p3 ∨ ((p2 ∨ p1) → p1))) → p1)) → p2) ∧ True)) ∨ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250949657093627015126578204606 : ((p1 → p4) ∨ ((p3 → (((p5 ∧ p3) ∧ p5) → ((p2 ∧ (p4 → (False ∨ (False ∧ False)))) ∨ p3))) ∨ ((p4 → (p1 ∨ True)) → (p4 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153152739725904892702210606604 : ((p5 ∧ (((p2 ∨ ((((p5 → (p3 ∨ p4)) ∨ p1) ∧ ((p2 ∨ (False → p3)) ∧ p1)) → False)) ∧ p1) → True)) → (p5 → ((p5 → False) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759067631922254598237581663285 : (((p2 ∧ ((p3 → ((p5 ∨ (p5 → (p4 ∧ (((p2 ∨ False) ∧ ((p5 → p4) ∨ (p2 → p1))) ∨ True)))) ∧ ((p4 → p4) ∧ True))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638587542415062581364370781903 : (((((p1 ∨ ((False ∨ (p5 → p4)) ∨ p2)) ∨ (p5 ∧ (p5 ∨ ((p3 ∧ (((p1 ∧ (True ∨ p1)) ∨ p2) → (True ∧ p1))) ∨ p1)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117464386800078824125864672149 : ((p1 ∧ ((p5 → False) → ((p1 ∧ (p3 ∧ (p2 ∧ (p4 ∧ (p3 → (p2 ∨ ((p1 ∧ False) → (p4 → p5)))))))) ∧ (p4 → p4)))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153002794507974353661303162662 : ((p1 ∧ (p5 → ((True → (((((p4 ∧ (False ∧ (p3 ∨ p3))) ∧ p2) ∧ (False → p5)) → p4) ∧ True)) ∨ False))) → (((True → p5) ∧ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147941727818648468828277889950 : ((((p2 ∨ False) ∧ (False ∧ ((True → p2) → ((p1 → ((p2 ∧ (p5 → p3)) ∧ p4)) ∧ p4)))) ∧ (True → True)) ∨ (False ∨ (True ∨ (p5 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52237431176210812773399577734 : (((p3 ∧ ((p3 ∨ p5) → ((p3 ∧ p3) → (True ∨ (((True ∧ p1) → p3) ∧ p2))))) → (((p1 → p5) ∨ p5) ∧ ((p4 ∧ p5) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349992929912734191862059641143 : (p4 → (((((((p2 ∨ (((p2 ∨ p1) → True) ∧ p1)) ∧ p4) ∧ False) ∨ True) → ((p5 → ((True ∧ p4) ∧ True)) → (p3 ∨ p1))) ∨ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680983877679783673711830355255 : (((((p5 ∨ p3) ∨ (True ∧ (((p1 ∧ True) ∧ p3) ∧ (((p3 ∧ (False → False)) ∨ (p1 ∨ p3)) ∧ p1)))) → (False ∨ (True ∨ (p5 ∨ p5)))) ∨ p4) ∧ True) := by
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
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h9.left
    let h15 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352205536958216967484474022679 : (p4 → ((True → (True ∨ (p3 ∧ p3))) ∧ ((p2 ∧ p4) → ((True ∨ p5) → ((((True ∧ False) ∧ p2) ∨ ((p2 ∧ p1) ∨ (p3 ∨ True))) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167568428438953893705268608892 : (((((((p2 → (False ∧ p4)) → p4) ∨ (p1 ∨ p1)) → p2) → (p2 ∨ p2)) ∨ (p3 ∧ p2)) → (p1 → ((p2 ∨ (p3 ∨ p1)) → (p5 ∨ p1)))) := by
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
    cases h1
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356034410613908365151457836754 : (p5 → (((p5 ∨ ((p3 ∨ p1) → p5)) → (True ∧ ((((p3 ∨ p2) ∧ p3) ∧ (p3 ∧ p3)) → (p1 ∧ False)))) ∨ (p5 ∨ ((p4 ∧ p5) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10178939490439073499707901157 : (((p1 ∨ ((p2 ∧ (False ∧ ((p5 ∨ ((p5 ∧ (((True → p1) ∨ True) ∨ False)) ∨ p2)) ∧ (True → True)))) ∨ (p3 → (p5 ∨ True)))) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57437036372423293938448771773 : (((p3 ∨ (p3 → p5)) ∨ (True ∧ (p1 ∨ ((p1 ∧ (p3 ∨ (False ∨ (p5 ∧ p3)))) → (False ∧ (p5 → (p5 ∨ ((p1 → False) → p2)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753985472800911161241074255031 : (((False ∧ ((p3 ∧ ((False → (p3 ∧ False)) → True)) → ((((True ∨ (p2 ∨ (p2 ∨ p4))) → False) ∨ (p3 → p2)) ∧ (p5 → (p4 → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_974555306988760878918389271363 : ((((p1 → p1) → ((((p1 ∨ ((p3 ∨ p2) ∨ p2)) ∧ (True → ((p5 ∨ (p3 ∨ p4)) ∨ True))) ∧ (((p2 ∧ False) ∨ p3) ∧ True)) ∧ p1)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207272537625636287928399855175 : (((((p5 ∧ p2) ∨ p5) → p2) ∨ True) → (((((p2 → p5) ∨ (p3 ∨ True)) → p2) → (((p4 ∨ True) ∧ ((p4 ∨ p2) ∨ p1)) ∨ p1)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((p2 → p5) ∨ (p3 ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : ((p2 → p5) ∨ (p3 ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65716029822465898458280550993 : ((p4 ∨ ((((p3 → ((p3 → (p1 ∨ p2)) → True)) → p4) ∨ (((True ∨ (p3 ∨ p1)) → True) ∧ (p1 ∨ (p2 ∧ p4)))) ∨ (p1 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197751924178367642976823451864 : (((p1 ∧ (p1 ∨ p4)) ∧ (p4 ∧ (p5 → True))) ∨ (((False ∧ p3) ∧ (True ∨ (False ∧ (p1 ∨ ((((p1 ∨ p3) ∧ False) → p5) ∧ p4))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189888464930173699065675948793 : ((p2 → (((p4 ∧ p3) ∧ (p3 ∨ p4)) ∨ (False → p2))) ∧ (p5 ∨ ((False ∧ (((p5 ∨ p5) → p1) ∨ ((p4 ∧ p3) → (p3 → p1)))) → p3))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313084093332118982675556883084 : (p3 ∨ (((((p4 → p3) ∨ (((False ∨ True) ∧ p3) ∨ (((True ∧ p1) ∧ p4) ∧ p1))) ∨ ((p3 ∨ (p1 → p1)) ∨ True)) ∨ (p3 → p3)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_137976838549099427821053867715 : ((p5 ∨ (((p5 ∧ (p2 ∧ (False → p3))) → p1) → (p1 → (((False → False) → (p5 ∧ p2)) ∧ ((p5 → False) ∨ True))))) ∨ ((p1 → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114543971140327343023368350788 : ((((((p5 → True) ∧ (((p1 ∧ p2) ∧ (p2 ∧ (p1 ∧ p1))) ∧ p2)) ∨ p1) ∧ p1) ∧ (((False ∧ p5) → (p3 ∧ False)) → p1)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260394154738319271565733076615 : ((p2 → p5) → (p3 → ((((p5 ∨ p2) → p1) → (p1 ∨ (p5 → (((p1 ∨ p5) ∨ (p4 ∨ (True → False))) ∨ (p3 ∨ False))))) ∨ (p5 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190346170366592629565206612261 : (((((False → p4) → p2) ∨ ((False ∧ p3) ∧ False)) ∨ True) ∨ ((((p2 ∨ ((True → p2) → True)) → p4) ∧ p2) ∧ ((p2 → p3) → (False ∨ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42172828596151338725575669916 : (((True ∧ (((p4 ∧ ((False → p3) → (p1 ∧ p1))) ∨ ((p4 → ((True ∧ True) ∧ (True ∧ p1))) ∨ (p3 ∨ (p1 → p5)))) ∧ p5)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164676863336127330529612334446 : (((((False ∨ (p1 → (((p5 → True) ∨ p2) → p3))) ∧ (p5 → (p5 → p2))) ∧ p5) ∨ p4) ∨ ((p3 → (p5 ∨ p4)) → (False → (p3 ∧ p4)))) := by
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
theorem thm_5_vars_65240791063644544895209160743 : ((p3 ∨ ((((p2 → (p1 ∧ p5)) ∧ ((((p1 → p1) ∨ ((p3 ∨ p1) ∨ (p3 ∨ (False ∧ p3)))) → (p2 ∧ p5)) → p3)) ∨ p1) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62055252420099529006993367175 : ((p2 ∧ ((True ∨ p2) → (((p3 ∨ True) ∧ ((p5 → p5) → p1)) ∨ ((p5 → (((p5 → (p4 ∧ p1)) ∧ p5) ∧ True)) ∧ (p2 → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148560323920971496089587111218 : ((((p2 → (p3 ∨ True)) ∧ ((p2 ∧ (p4 ∨ p5)) ∨ p2)) ∧ (((p3 ∧ (p3 → (p4 ∨ p5))) ∨ p5) ∧ p2)) ∨ (False → (p2 ∧ (p2 ∨ p4)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113290453564085133057990443438 : ((((((True ∨ p4) ∨ p2) → (p2 → (False ∨ (p3 → True)))) → (((p1 → (p5 ∧ p4)) → False) ∧ (False ∧ p3))) ∧ (p4 ∨ p1)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605596843680318958128625834121 : ((((p4 → (((p4 ∨ ((((p3 ∨ (p4 → (p3 ∧ p5))) → p3) ∧ (p3 ∨ (p3 ∨ (p3 ∨ (p1 ∧ p5))))) ∨ p2)) → False) ∨ False)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2688611442465392708957985356 : (((((p5 ∧ p2) ∧ False) ∨ True) → False) → ((p3 → ((p4 ∨ p4) ∧ (((((p5 → p2) ∨ p5) → p5) ∧ p2) ∧ p2))) ∨ (True ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ p2) ∧ False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158129524793276915443011529827 : ((((p3 ∨ (False → p2)) ∧ p2) ∨ (((((p5 ∨ p1) ∨ True) → (p2 ∨ p1)) ∧ (p5 ∨ p1)) ∨ True)) ∨ (p3 ∧ ((p3 ∨ (p5 ∧ p4)) → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49701931079774344575601298671 : ((((p4 ∧ p5) → (p4 ∧ (p2 ∧ (((p2 ∨ (False → (p2 → p4))) → ((p2 ∨ p2) ∨ (p5 → True))) → p2)))) → ((p3 ∧ p2) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158209900105660798026319776597 : ((((p5 ∧ True) → p5) ∧ (p2 ∨ (False ∨ (((((p4 ∧ False) ∨ p4) ∨ (p4 → p2)) ∨ True) ∨ False)))) ∨ ((((p3 → p4) ∨ False) ∨ p2) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41898018688701843732689666757 : (((((p5 ∧ p2) ∧ p1) → ((((p5 ∨ (p3 → False)) → p5) → (p4 → ((((False → (p2 ∧ p4)) → p5) → p4) → False))) ∨ False)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_912548283689681752261352823500 : (((((p4 → ((True → (p5 ∧ ((True ∧ p3) ∨ p3))) ∨ ((p2 ∨ p2) ∨ False))) ∨ (p5 ∨ True)) → (((True ∧ p5) ∨ True) ∧ (p1 ∨ p1))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 → ((True → (p5 ∧ ((True ∧ p3) ∨ p3))) ∨ ((p2 ∨ p2) ∨ False))) ∨ (p5 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_93024913174380754695072504458 : ((True ∧ (((((((p2 ∨ p2) → p5) → True) → (((False ∧ p5) ∧ p1) ∧ p4)) ∨ False) ∨ p2) ∧ (False → (p1 ∨ ((p5 ∨ p2) ∧ p5))))) → p2) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : (((p2 ∨ p2) → p5) → True) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h10 := h7 h8
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158238133616700647006502843885 : ((((False ∧ p5) ∧ p5) ∨ (((p5 ∧ False) ∨ (p1 → p3)) ∨ (p4 ∨ ((p4 → (p1 → p4)) ∨ p5)))) ∨ (((p2 → (p1 → False)) ∨ False) ∧ p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231119573416797340656559852655 : (((p1 ∨ False) ∨ p2) → (((p4 ∨ (p3 ∨ (p4 ∧ True))) ∧ p3) ∨ (p2 ∨ ((((p3 ∧ ((p4 ∨ p5) → p4)) ∧ p4) → (p3 → p4)) ∨ p1)))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328718434548956744408918324852 : (True → ((p1 → ((((p1 ∨ p4) ∧ (p4 ∨ p3)) ∧ p3) ∧ (p4 ∨ p4))) ∨ (((p3 → ((p2 ∧ p5) ∨ p2)) ∨ (False ∨ (p2 ∨ True))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_174933955848349535092189120239 : (((p1 → p4) → ((((p2 ∧ (p1 ∧ False)) → p1) → (False ∨ (p5 ∨ p4))) ∨ p5)) → (p5 ∨ (((p2 ∨ p1) → False) ∨ (True ∨ (p2 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179345794773403274651010608405 : ((p1 ∨ (p1 ∨ (p5 ∨ (p1 ∨ (p2 ∨ ((p5 ∨ p2) → (p4 ∨ True))))))) ∨ (((True ∧ ((p2 ∧ (p3 ∧ p5)) ∨ (p3 → False))) ∧ p3) ∧ p4)) := by
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
theorem thm_5_vars_112154523895284038524934206847 : (((p2 ∧ (((((p3 ∧ p4) ∨ (p1 ∨ p4)) ∨ p3) → (p3 ∧ (((p5 → True) → p5) ∧ (p4 ∨ p3)))) → (p4 ∨ p5))) ∨ p5) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190994381492845220769358171040 : ((((p2 ∧ False) ∨ (p1 ∧ False)) ∨ ((True ∨ True) → p2)) ∨ ((p4 ∨ p3) ∨ (((p4 ∨ p4) → ((((p5 → False) ∨ p5) ∨ True) ∨ False)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47200309621642961837436544160 : ((((((False → p4) → p1) ∧ (p3 → (((True ∧ p5) ∧ True) ∧ p2))) → ((p1 ∧ (p4 → ((p3 → True) → True))) ∧ True)) ∨ (True → p1)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64796608207122527581107329875 : ((p2 ∨ (((p4 → p1) ∧ ((((True → p5) ∧ p4) ∧ (p2 ∨ ((p2 → p4) ∧ ((p4 → (True → (False ∨ p2))) → p5)))) ∧ p3)) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153036545537686022246101954302 : ((p2 ∧ ((p3 → p4) → (((p5 → (((True ∨ True) ∧ p3) ∨ (p2 ∧ ((p5 ∧ p4) → True)))) → p1) ∧ False))) → (p4 → ((p3 ∧ False) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p3 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : (p3 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h13 := h10 h11
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- False on the left can always be used.
  apply False.elim h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h1.left
  let h16 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187002740817810968070302122500 : ((((p4 → p5) ∨ p2) → ((p4 → (True ∨ (p4 → p2))) ∧ p1)) → ((p1 ∧ (((True ∧ p4) → ((False ∧ True) → p5)) ∧ (p4 ∧ p3))) → p1)) := by
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
  let h7 := h6.left
  let h8 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337079529723598472274588065888 : (p1 → (((p3 ∨ (((p4 → p3) ∧ p1) ∧ ((((p3 ∨ p3) → (p5 ∧ p2)) ∨ (p5 ∨ False)) ∧ p3))) ∨ ((p1 → p4) ∨ False)) ∨ (p2 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51693475143733740287317007927 : ((((p1 ∨ ((False ∧ p3) → (p5 ∨ ((p2 ∨ p1) → (p1 ∧ p1))))) → (p3 ∧ p2)) ∧ (p3 → ((True → (p1 ∧ (p3 → p2))) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338223952550843222582952769720 : (p1 → (((False ∨ (p3 ∧ (p2 → False))) ∧ p3) ∨ ((p5 → p5) → ((p3 ∧ (p1 ∧ (p5 → p5))) → (True → (False ∨ (p3 ∧ (p4 → p1)))))))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Implications on the right can always be decomposed.
  intro h9
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216713812697735352289270128764 : ((((p4 ∧ p2) → p1) ∧ p5) → (((p1 ∧ ((p4 ∨ p5) → False)) ∧ (True ∧ (p4 ∨ p2))) → (p4 ∧ (p3 ∧ (((p3 → p4) ∧ p1) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h15 : (p4 ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h16 := h6 h15
    -- False on the left can always be used.
    apply False.elim h16
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h17 := h2.left
  let h18 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h17.left
  let h20 := h17.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h18.left
  let h22 := h18.right
  -- Disjunctions on the left can always be decomposed.
  cases h22
  case inl h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h1.left
    let h25 := h1.right
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h26 : (p4 ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h23
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h27 := h20 h26
    -- False on the left can always be used.
    apply False.elim h27
  case inr h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h1.left
    let h30 := h1.right
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h31 : (p4 ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h30
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h32 := h20 h31
    -- False on the left can always be used.
    apply False.elim h32
  -- Conjunctions on the left can always be decomposed.
  let h33 := h2.left
  let h34 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h35 := h33.left
  let h36 := h33.right
  -- Conjunctions on the left can always be decomposed.
  let h37 := h34.left
  let h38 := h34.right
  -- Disjunctions on the left can always be decomposed.
  cases h38
  case inl h39 =>
    -- Conjunctions on the left can always be decomposed.
    let h40 := h1.left
    let h41 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h42 =>
    -- Conjunctions on the left can always be decomposed.
    let h43 := h1.left
    let h44 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217574919349147782989450120468 : ((((False ∨ p5) ∨ False) → False) → ((p1 → ((((p3 ∧ p3) → (p4 → p5)) ∧ ((True ∨ (p2 → p4)) → p2)) ∧ (p3 ∧ p4))) ∨ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248307790312374275999564298378 : ((p2 ∨ p2) ∨ (p1 → (p4 ∨ ((p4 ∧ (((p5 ∧ (p2 ∨ p3)) ∧ p3) ∨ (False → (((True ∧ (p5 → True)) ∨ (p1 ∨ p5)) ∧ p2)))) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67512665268151198412878757833 : ((p1 → ((p3 → ((((True ∨ p5) ∧ True) → p5) ∧ p1)) → ((p1 → (p3 ∨ (((p5 ∧ (p2 → (p4 → p3))) → p2) → p3))) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149181772466630317434104770213 : (((False → p5) ∧ (((False ∨ p2) ∨ (((p5 ∧ ((p2 ∨ (p2 ∧ p2)) ∧ False)) ∧ p5) ∧ (p4 ∧ p2))) ∨ p2)) ∨ (False → ((True ∧ True) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2661217882632440904864801029 : (((p1 ∨ p3) ∧ (False ∧ (p1 ∧ p3))) ∨ (False → (((p2 ∧ (((p2 ∧ (p5 ∨ p2)) ∧ p2) → ((False ∨ p2) → p3))) ∧ p4) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h2.left
    let h7 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h1
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355782921306404943232996816548 : (p5 → ((((p1 ∧ (p2 ∨ ((True ∧ (((p2 ∧ True) ∧ ((p1 ∨ False) → True)) ∧ p3)) ∧ p4))) ∨ p5) ∨ (p5 ∨ p1)) ∧ (p2 → (p5 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186180415154863952359519712236 : (((p2 ∧ ((p2 ∧ p4) → (p2 ∨ (False → (False ∨ p5))))) ∨ p2) → (((p2 → p4) ∨ (((True ∧ p4) → p5) ∧ p3)) ∨ ((p1 ∧ False) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227803016814948812923573972490 : ((p1 ∧ (p5 → p3)) ∨ (p5 ∨ ((((((((True ∨ True) → p5) ∨ True) ∧ True) ∧ (p5 ∨ p2)) → (((p1 ∨ False) ∨ p5) ∨ True)) ∨ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191514581743309848915099903555 : ((False ∧ (((True → False) ∧ p1) ∨ (p5 ∨ (p1 ∧ True)))) ∨ (((p4 ∧ ((p5 ∧ (p4 → p2)) ∧ (False ∨ p4))) → (p3 ∨ (True → p5))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164839688007631818421379107322 : (((p2 ∧ ((p3 ∨ True) ∧ ((p1 ∨ False) ∧ (True → (p5 ∨ ((p3 → True) → p1)))))) ∨ p3) ∨ ((False → ((p3 ∧ (False ∨ p5)) → False)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136903227168373965713791616898 : (((p5 ∨ p2) ∨ ((p5 ∨ ((p3 ∨ p4) ∧ (((True ∧ (p1 ∨ p1)) → False) ∨ (p4 → p4)))) ∧ ((p1 ∧ p1) ∨ False))) ∨ (p2 → (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636622437861051789101389918168 : ((((((p2 → (((((True → p1) ∨ p4) ∧ p4) ∧ (p3 ∧ p3)) ∨ p4)) ∧ p4) ∨ (((p4 → False) ∧ p5) ∧ (True ∧ (p1 → p1)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168909576701041976921950340701 : ((p5 ∨ ((p3 ∧ (p2 ∨ False)) ∨ ((p2 → (p3 ∧ (p5 → ((p1 → False) ∨ p1)))) → p3))) → (((True → (p3 ∧ p1)) → (p1 → p4)) ∨ True)) := by
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
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148025904712664714872186327766 : (((((p2 → (False ∧ p3)) → p3) ∧ (((p3 ∧ ((False ∨ p5) → (False ∧ p4))) ∨ False) → p5)) ∨ (p4 → p4)) ∨ (p5 → (False ∨ (p1 → p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137929077652222326805238187316 : ((p4 ∨ (False ∨ (((p5 ∨ (p5 ∧ (p2 ∨ ((((False ∨ p4) ∨ True) → (False → p4)) ∨ p1)))) ∨ (p2 → p3)) ∨ p4))) ∨ (p3 → (p3 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191097756484941151918738388919 : ((((p5 ∧ p4) → p4) ∧ (p3 → ((p1 ∨ p3) ∧ p2))) ∨ (((p3 ∧ ((p4 ∧ p5) → False)) → p1) ∨ ((((p3 ∧ p5) ∧ p2) ∧ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233553484817547379999930041943 : ((p1 ∨ (True → p1)) → ((((((p5 ∨ p2) ∧ ((p5 ∧ False) ∨ True)) → p1) ∨ (p5 ∧ (p3 ∨ p1))) ∧ p4) → ((p5 ∨ p4) ∧ (p5 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
  -- Conjunctions on the left can always be decomposed.
  let h17 := h2.left
  let h18 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h22 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h23 := h21 h22
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h23
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h28 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h29 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h25
    case inr h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h31 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h32 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172425459370435368112938229111 : (((True ∧ (p3 ∧ (False ∧ False))) ∧ ((p2 → (p4 ∨ p2)) → ((p5 ∧ True) → p1))) ∨ (True → (((p4 → (False → (p5 ∨ False))) → p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628225251063949890217321241507 : ((((((p3 → True) ∧ ((((p1 ∧ ((p1 → True) ∨ p2)) ∨ (True → p2)) ∨ ((((False → p2) ∧ p3) ∧ p2) ∧ p3)) → p1)) ∧ p4) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41275937607844197544050678109 : (((((((p4 → ((False → (p4 ∨ p5)) ∧ ((True ∧ p3) ∨ p4))) ∧ (p2 ∨ p1)) ∧ p2) ∨ p1) → (((p3 ∨ p4) ∧ p4) ∧ True)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147321731323198784677483226876 : ((((((((p4 ∧ (False ∨ (p3 → True))) → p5) ∨ p1) → ((p4 → p5) ∧ p1)) ∧ p2) ∧ (p4 ∨ p5)) ∨ p2) ∨ (False → (p3 ∧ (p4 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137725899230729838297208949471 : ((p1 ∨ (p1 ∧ (False ∧ (p5 ∨ ((p4 ∨ ((p1 → (((p1 ∧ p4) ∨ p4) ∧ ((p2 → p2) ∨ True))) ∨ p5)) → False))))) ∨ ((p4 → True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259650339394632381032389232409 : ((p1 → False) → ((p1 → p2) → ((((((p3 ∧ (False ∨ p1)) ∧ (((p4 ∧ True) → p3) ∨ False)) → (False ∨ p2)) ∨ False) → (True → p1)) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((p3 ∧ (False ∨ p1)) ∧ (((p4 ∧ True) → p3) ∨ False)) → (False ∨ p2)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h12 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h13 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h14 := h1 h13
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h16 := h3 h4
  -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
  have h17 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h16, we can now drive its conclusion.
  let h18 := h16 h17
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h19 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h18
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h20 := h1 h19
  -- False on the left can always be used.
  apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56923017681376170063023450292 : (((True ∨ (p4 ∧ p2)) ∧ (p2 ∨ (((((True → ((p2 ∧ (p2 ∨ p5)) ∧ p2)) ∨ (p1 ∧ ((True ∧ True) → p2))) → p2) → False) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110915950134937048826353739595 : ((((p2 ∨ ((p3 ∧ (((False ∧ p4) → True) ∧ (p1 ∨ ((False ∨ False) ∨ (p1 ∨ (p2 → (False → True))))))) ∧ p2)) → p1) ∧ False) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52808312799539600754047647211 : (((((p5 ∨ ((True ∨ p4) → True)) ∨ p3) ∨ ((p5 ∧ p4) ∧ (p2 ∨ p2))) → (p4 ∧ ((((p5 ∧ p5) → (p2 ∧ p2)) ∨ p4) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116337737964969519636377011574 : ((((p3 → p5) ∧ True) → ((p2 ∨ ((True ∨ (True ∧ True)) → (p1 → (True ∧ (p4 → (p3 ∨ (p2 ∨ (p3 → p4)))))))) → p1)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52434235029398152702646709845 : ((((True → True) → ((False ∧ p3) ∨ (p5 → ((p2 ∨ (p2 ∨ p2)) → p5)))) ∧ ((False ∧ (((p1 ∨ p2) ∧ p2) ∨ (True → p1))) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51344981747671044895282987313 : (((p5 → ((True → p2) → ((((p4 ∧ p3) → (p1 → ((p1 ∧ p4) ∨ p5))) ∧ p1) → p3))) ∨ ((((True ∨ True) ∧ True) ∨ p5) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



