variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313116166624612096831247644907 : (p3 ∨ (((((True ∧ (True → ((p3 ∨ p4) ∧ (p5 → ((p3 ∨ p5) → p3))))) ∧ True) ∧ (True ∧ (True → p5))) → (p3 ∧ (p1 → p3))) ∨ p4)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h13 := h7 h12
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
  have h15 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h14, we can now drive its conclusion.
  let h16 := h14 h15
  -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
  have h17 : (p3 ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h16, we can now drive its conclusion.
  let h18 := h16 h17
  -- One of the premise coincides with the conclusion.
  exact h18
  -- Implications on the right can always be decomposed.
  intro h19
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h20.left
  let h23 := h20.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h22.left
  let h25 := h22.right
  -- Conjunctions on the left can always be decomposed.
  let h26 := h21.left
  let h27 := h21.right
  -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
  have h28 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h27, we can now drive its conclusion.
  let h29 := h27 h28
  -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
  have h30 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h25, we can now drive its conclusion.
  let h31 := h25 h30
  -- We need to get the right conjuct of h31 based on <expert-advice>.
  let h32 := h31.right
  -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
  have h33 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h29
  -- We have shown the premise of h32, we can now drive its conclusion.
  let h34 := h32 h33
  -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
  have h35 : (p3 ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h29
  -- We have shown the premise of h34, we can now drive its conclusion.
  let h36 := h34 h35
  -- One of the premise coincides with the conclusion.
  exact h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200474729443088087439704521213 : (((p5 → p3) ∨ (p3 → (p5 ∨ (True ∨ True)))) → (((p1 ∨ (((p2 ∨ p4) ∨ (p1 → p1)) ∧ p1)) ∨ ((p5 → p2) ∧ (p4 ∧ p3))) ∨ True)) := by
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
theorem thm_5_vars_906263870906296782206008703161 : (((((((True ∨ ((True ∧ p3) ∨ (p2 ∨ (p2 → (True ∨ False))))) → False) ∧ ((p2 ∨ True) → p1)) ∨ True) → (p2 ∧ ((p2 → p4) → p1))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((True ∨ ((True ∧ p3) ∨ (p2 ∨ (p2 → (True ∨ False))))) → False) ∧ ((p2 ∨ True) → p1)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185268011550024968995951908902 : ((p1 ∧ (p3 ∧ ((p3 ∨ ((True ∨ p2) → p1)) ∨ (p5 ∧ p2)))) ∨ (p4 ∨ ((p5 → (((False ∧ False) ∨ p1) → (False ∨ p1))) ∨ (p2 ∧ p3)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165731614644304528006904651739 : (((((p4 ∨ p3) ∧ False) ∧ p2) ∨ (p4 → (((p2 ∧ p5) → ((p3 ∨ p2) ∨ p3)) ∨ p3))) ∨ (((p3 ∧ ((p3 ∨ p5) → p2)) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353490394553097744848266608238 : (p4 → (p2 ∨ ((((p4 → ((p2 ∧ p4) ∨ p1)) → (True ∨ p3)) → (((p5 → p5) ∧ (p3 ∨ True)) → False)) → ((False ∧ p3) ∧ (p2 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p4 → ((p2 ∧ p4) ∨ p1)) → (True ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((p5 → p5) ∧ (p3 ∨ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h9 : ((p4 → ((p2 ∧ p4) ∨ p1)) → (True ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h9
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : ((p5 → p5) ∧ (p3 ∨ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h13
    -- One of the premise coincides with the conclusion.
    exact h13
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h14 := h11 h12
  -- False on the left can always be used.
  apply False.elim h14
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219329908659809458808549924348 : ((p2 ∨ (False ∨ (True ∨ p5))) → ((((p1 ∨ p5) ∨ (p4 ∨ ((p3 ∧ p1) → (p4 → (p4 ∨ (p2 ∧ p4)))))) ∨ (True ∨ (p5 ∨ p3))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2447363953597715150225418264 : ((((((p3 → (p5 ∧ True)) → p2) ∨ p2) ∨ True) ∧ False) ∨ (((p5 ∧ ((((p4 → p5) → p5) ∨ (p3 ∨ p1)) ∨ p3)) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207754485501874264695539603350 : (((False ∨ (p1 → (True → p1))) → p5) → ((p4 ∧ ((p1 → (True → (p4 → False))) → (False ∨ (((p3 ∧ p2) ∧ (p3 ∧ p2)) ∧ p4)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ (p1 → (True → p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649586595695091086622115623580 : (((((((p2 ∧ (p5 → p3)) → ((p3 ∧ (p1 → (p1 ∧ (((p4 ∧ p2) → False) ∧ p2)))) → True)) → p4) ∨ (False ∧ True)) ∧ (False ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328424644191409719520780187460 : (True → (((False ∨ False) ∨ ((p5 ∨ p4) ∨ (((p4 ∧ p2) ∧ p5) ∧ ((p3 ∨ (False ∨ p3)) ∧ p3)))) ∨ ((p4 → (p1 → (True → True))) ∨ p2))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158325690848938491317242424019 : (((p5 → (p3 ∧ p1)) → ((((p2 ∧ p4) ∨ p4) → (True ∧ (p3 ∨ p5))) ∨ (p1 ∨ (False ∨ p5)))) ∨ ((p1 ∧ (p2 ∧ (True ∧ p1))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321718797012548977991019465284 : (p4 ∨ (p5 → (((((p3 ∨ ((((p1 ∧ True) ∧ p3) ∨ p3) → True)) → p1) ∨ p4) ∨ ((p2 → p3) → (((p3 → False) ∧ p2) → p1))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111835384615339318930619823374 : (((((((((p5 ∧ False) ∨ False) ∧ p3) ∨ (p5 ∨ ((p1 → p4) ∨ False))) ∧ p1) ∧ (p4 → p5)) ∨ (p1 → (p1 ∧ p1))) ∨ p4) ∨ (p1 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185296217368243296860454384055 : ((p2 ∧ (True ∧ ((p3 → ((p3 ∧ True) → p5)) → (p5 ∧ p4)))) ∨ (p1 ∨ ((p5 ∨ p3) ∨ (p4 → ((p2 → ((p4 → p3) ∨ False)) → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707416204528700015199252230822 : (((((p2 → (p3 ∧ (p4 → p1))) → (p5 ∨ p5)) ∨ (False ∨ (p5 ∨ ((p4 → (p5 → p5)) ∨ (p5 ∨ ((False → p3) ∧ (p3 → p3))))))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40161369982203732698906741971 : ((((((((True → (p1 ∨ p5)) → False) ∨ p5) → (True ∧ False)) → ((p4 ∨ (False ∧ p3)) ∨ ((p4 ∧ p5) → (p2 ∧ p2)))) ∧ p3) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788886892565739717046434130091 : (((p5 ∨ (((False ∨ p5) ∨ (True ∨ ((((p2 ∨ ((p5 ∧ True) ∨ False)) → (p5 ∨ (p1 → p1))) → (p2 ∨ p2)) ∧ p1))) ∧ (p5 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683632460315018372840028721304 : ((((((((True ∨ p2) → ((p3 ∧ p3) ∧ True)) → p4) ∧ ((p5 → False) ∨ (p1 ∧ p3))) ∧ p2) ∨ (p5 → (p1 → (p3 → (p3 ∧ True))))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180915244249863148344030317291 : (((p4 → (False ∨ p4)) → ((True → (p2 → p1)) ∧ (False ∧ (False → p2)))) → ((p3 → ((((p4 ∨ True) ∨ p2) ∨ p5) ∧ False)) ∨ (p1 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137135471245774937658692667196 : ((True ∧ (False ∨ ((((p3 ∨ False) ∨ ((p5 → True) → (p1 ∨ p3))) → (((p3 → True) → p5) ∧ (p4 → False))) ∧ p1))) ∨ ((p1 ∨ False) → p1)) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351836364199259397199979852538 : (p4 → ((((((p5 ∨ (True ∨ p3)) ∨ (False ∧ p3)) ∨ p5) → p4) ∧ p3) → (((p2 ∨ (p4 ∨ (p2 ∧ (p5 → (p2 → p2))))) → p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190127205898180762535399597284 : ((((p3 ∧ (p4 ∧ p4)) → ((p2 ∨ p2) ∨ p3)) ∧ p1) ∨ ((True → (p2 ∧ ((((p2 ∧ (p2 ∨ True)) ∧ True) ∨ p3) ∧ (False → p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56572722405180379096717628532 : (((True → (p3 ∨ (p2 ∨ p2))) → ((True ∨ False) → (((p2 ∨ p1) ∨ ((p2 → ((p1 → p3) ∧ p4)) ∧ p1)) ∨ ((False → p4) → True)))) ∨ p5) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40974806109321597751668567684 : (((((p1 ∧ p3) ∧ (p4 ∧ (p2 ∧ (((p2 ∨ p4) ∧ (p5 ∧ False)) ∨ ((((p4 ∨ p2) → p5) ∨ True) → p1))))) ∨ (p2 ∧ p3)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75717549104006887832333631120 : (((((p1 ∨ ((((p5 ∧ True) ∧ p1) ∧ (p3 ∧ (((p2 → (p2 ∨ False)) ∨ (p1 ∨ False)) → p1))) → p4)) ∧ (p4 → p5)) ∨ True) → p4) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ ((((p5 ∧ True) ∧ p1) ∧ (p3 ∧ (((p2 → (p2 ∨ False)) ∨ (p1 ∨ False)) → p1))) → p4)) ∧ (p4 → p5)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597581721339986724927892182737 : (((((((True ∨ p2) ∨ p4) ∧ p1) → ((p4 ∨ ((p3 ∨ p5) ∨ (p4 ∧ p2))) ∧ (((((p4 → p3) → False) ∨ False) ∨ True) ∧ False))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314423121470619640539260110232 : (p3 ∨ (((((p1 ∧ (True → p1)) → p3) ∧ (p2 ∧ False)) ∨ ((((False ∨ p3) → False) ∨ p3) ∨ (p4 ∨ p2))) ∨ ((True → (p1 ∧ p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743044607954509848063560168377 : ((((p4 → False) ∨ (((p4 ∨ p4) ∧ ((p2 → ((p3 ∧ p1) ∨ (False ∨ p4))) → False)) → (((((p4 → p2) ∧ p3) ∧ p1) ∨ p4) ∨ p5))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164102840803262798472662741601 : ((p2 ∨ ((p3 ∨ (p4 ∧ p5)) ∨ (((False → p3) → (p2 ∧ (p4 ∧ p3))) → (p4 ∧ True)))) ∧ (p3 → ((((True ∨ False) ∨ p3) ∧ False) ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265900568907367771532610180880 : (True ∧ (True → ((((p4 ∧ (p2 ∧ p2)) → p1) → ((p3 ∧ p1) → p2)) ∨ (((((False ∨ ((p2 ∧ p1) → p4)) → p4) ∧ True) → True) → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752772984812643030712866026574 : (((False ∧ (((p5 → p4) → ((True ∧ (((p4 ∨ ((p1 ∨ p5) → (p4 → p2))) ∧ ((p5 ∧ p5) → False)) ∨ (p3 ∨ p4))) ∨ p4)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115744759286852722456008254223 : ((((p1 → p2) ∨ ((True → p1) ∨ p5)) → (((True ∧ p3) → p5) → ((((True → True) ∨ (p4 ∨ p5)) → p2) ∧ (p3 → p2)))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216277153321605325803811458825 : ((p2 → ((p3 ∧ p1) ∧ p4)) ∨ (p4 → (p5 → (p1 ∨ ((p4 → (((False ∧ p4) ∨ ((False ∨ (False ∧ p3)) ∧ p5)) ∨ (True ∨ p1))) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149839983533179841279588015745 : ((p1 ∨ (((p3 ∨ True) ∧ p1) ∨ (((p4 ∧ (p2 ∨ p1)) ∧ p5) → ((p5 → (False ∧ (p1 → p1))) → p3)))) ∨ ((True ∨ p1) → (True ∧ p1))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h12
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57875390984868778892230016574 : (((p1 ∨ (True → False)) → (((p2 ∧ (p1 → (p5 → ((p2 ∨ ((False ∨ p1) ∨ p2)) ∨ p2)))) ∨ p1) ∧ ((True ∨ p5) ∨ (True ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116365148323083350600186691375 : ((((p2 ∧ False) → p4) → (True → (((p3 ∧ (p4 ∧ p1)) ∧ (p2 ∧ (True → p2))) ∨ ((p1 → p4) ∧ ((True ∨ p5) → p4))))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677466786899042389986687734252 : (((((((((p1 ∨ True) ∧ (p3 ∨ p1)) → p3) ∨ p5) ∨ (((p5 → True) ∧ p3) ∨ (True → p5))) ∨ False) ∨ (False → (p1 → (p4 ∨ False)))) ∨ p2) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78027135610011205141469933312 : (((p5 ∨ (((((p4 → p1) → (p1 → ((False → p4) ∨ (False ∨ p5)))) → ((p1 ∨ p3) ∧ (False ∨ (p5 ∧ p1)))) ∧ p1) → p5)) → p2) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ (((((p4 → p1) → (p1 → ((False → p4) ∨ (False ∨ p5)))) → ((p1 ∨ p3) ∧ (False ∨ (p5 ∧ p1)))) ∧ p1) → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : ((p4 → p1) → (p1 → ((False → p4) ∨ (False ∨ p5)))) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h6
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h14
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164849196193743924430983461707 : (((p5 ∧ ((p1 ∧ p4) ∧ (p1 ∨ ((False → p5) ∨ (((p5 ∨ p2) ∨ p1) → False))))) ∨ p5) ∨ ((p1 ∨ (True ∨ p1)) ∧ (p2 → (False → p2)))) := by
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
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325786182250344853636936718351 : (p5 ∨ (p2 ∨ (p4 → (p5 → ((((p1 ∧ (((p5 ∨ False) → p3) ∧ (p1 ∧ (p3 ∧ ((False ∨ p1) → p2))))) ∨ p5) ∨ p1) ∧ (p2 → p4)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156888701189949986839671283301 : ((((((p5 → (True ∨ True)) ∧ (((p2 ∧ False) ∨ p5) ∧ p1)) ∨ (p3 ∨ (p2 → p4))) ∨ True) ∨ p1) ∨ (((p5 ∨ (p4 ∧ p3)) ∨ p1) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41237393928592661680693921199 : ((((p2 ∨ (p5 → (p2 → ((p5 → ((p1 ∨ False) → ((p2 ∧ p2) → (p2 → p3)))) ∧ p3)))) ∧ (p3 ∧ ((p5 → p2) → p1))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308427707292237352898368510073 : (p2 ∨ ((((p1 → ((p2 ∧ (p5 ∧ True)) ∧ p2)) ∨ (((p3 ∨ ((True ∧ (p3 → (True → (p2 ∨ p3)))) → False)) ∨ p3) ∧ p3)) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259432484154031086928490219774 : ((False → p4) → (((((p5 ∨ (((True → p5) ∨ p1) → False)) → p3) → (p3 → ((p5 → p2) ∧ (True → False)))) → (p2 ∨ (True ∧ True))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48693570837435936623213833908 : (((((((True ∧ (True → p1)) ∧ p2) ∧ p1) → p2) → ((p5 ∧ (False ∨ p2)) → ((p4 → False) ∨ (False ∧ p4)))) ∧ (p2 ∧ (p2 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356030051288690016134552630540 : (p5 → (((((False → p2) ∨ (True ∧ (True ∧ p1))) → False) ∧ ((((True ∧ p1) ∧ p2) ∧ (p4 ∨ p2)) ∨ p2)) ∨ ((p5 → p1) → (p5 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207678594254756685160748928208 : ((((False ∧ p1) → (True ∧ p1)) → True) → (((p5 ∧ ((p3 ∧ ((p2 ∧ p2) ∧ p5)) ∧ ((p5 ∨ True) → ((p3 → p2) ∧ p3)))) ∨ True) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232160683189019486268075994358 : (((True → p3) → p3) → ((p2 ∨ ((p2 ∨ p1) → False)) ∨ (False → ((False ∨ (((p3 → True) ∨ False) ∨ p5)) ∨ ((p5 → p3) ∧ (True ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255084129217998226156685379813 : ((p4 ∧ p2) → ((p3 ∨ (((p4 ∨ False) ∧ p3) ∨ (p2 → True))) ∧ (((p3 ∧ (True ∨ (p5 → p4))) ∨ p1) ∨ ((p1 ∨ True) → (p3 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4265296246781671471565772682 : (True → ((((p1 → (((p3 → True) ∨ True) ∨ (((p5 → p5) ∨ (((p5 → False) → p2) ∧ p1)) → p1))) → (p4 ∨ False)) ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87203998372268448039574293744 : (((p5 → ((False → ((False → False) ∨ p5)) ∨ p5)) → (((p1 ∧ p2) ∨ (p5 ∧ ((((p4 ∧ p1) ∨ (False ∧ False)) → True) ∨ p2))) ∧ False)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → ((False → ((False → False) ∨ p5)) ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53630029857092815134796525556 : (((((p5 ∧ (p4 ∧ False)) → True) ∨ (p2 ∨ (p1 ∨ p4))) ∧ ((True → ((((p1 ∧ (p5 ∨ True)) ∧ False) → True) → p3)) ∧ (p5 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183452779938036525628210072247 : ((p2 ∨ ((p2 → (False → (p2 → p5))) → ((True → p1) → p1))) ∧ ((((p1 ∧ (p4 ∨ p1)) ∧ p5) ∧ (p5 ∨ False)) → (p2 → (False ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627453044336757172050564317606 : ((((((True ∨ (((True → p5) ∧ p2) ∧ (True ∧ (((p1 ∧ p5) → False) ∧ ((((True ∧ p5) ∧ p2) → p1) ∧ True))))) → p1) ∧ True) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216932544774589828959668685558 : (((True → (True → False)) ∧ p1) → ((((p5 ∧ ((True → ((True ∨ p5) → False)) ∨ ((p2 ∨ p2) ∨ p1))) ∧ p3) ∨ (p3 ∨ True)) ∨ (p3 ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736159167627340791654109985195 : ((((False → False) ∧ (((p2 ∨ (p3 ∨ p1)) → (p1 → p2)) → ((((True ∨ p3) ∧ (((p2 ∨ False) ∨ p2) ∧ (p5 → True))) ∧ False) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204429030925568678547444702039 : (((((False ∧ False) ∧ p3) ∧ False) ∨ p3) ∨ ((p1 → ((p3 ∧ ((p1 ∧ (p2 ∧ p5)) ∨ p3)) ∨ p2)) ∨ (((False → False) ∧ True) → (False → p1)))) := by
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
theorem thm_5_vars_358216871110173789147729562701 : (p5 → (p4 ∨ (((((p2 → p4) ∨ (((False ∧ (p2 → p2)) ∧ (p3 ∨ p5)) → (p2 ∨ (p3 → p5)))) ∧ p4) → (p1 ∨ (p5 ∧ p1))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614404562336287633655084948993 : (((((p5 ∨ (((((True ∧ (((False → p3) ∨ p4) ∧ p3)) ∨ (p5 → True)) ∧ True) ∧ (p3 ∨ p1)) ∨ True)) → (p5 ∨ (False → False))) ∨ p3) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h6
          case inl h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h16
            -- False on the left can always be used.
            apply False.elim h16
          case inr h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h18
            -- False on the left can always be used.
            apply False.elim h18
        case inr h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h6
          case inl h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h21
            -- False on the left can always be used.
            apply False.elim h21
          case inr h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h23
            -- False on the left can always be used.
            apply False.elim h23
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h26
          -- False on the left can always be used.
          apply False.elim h26
        case inr h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h28
          -- False on the left can always be used.
          apply False.elim h28
    case inr h29 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h30
      -- False on the left can always be used.
      apply False.elim h30
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53269965859303166596731003936 : (((False ∧ ((((p5 → p2) ∧ True) ∨ (True ∨ p2)) ∧ (p5 ∨ p5))) ∨ ((False ∧ (((p5 → (p5 ∨ (p1 ∨ False))) ∧ p1) ∧ p2)) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166217696737372379936987611489 : ((p2 ∧ (((p1 → (True → ((p5 ∧ ((p2 ∨ (p5 ∧ p3)) → p5)) → p3))) ∧ p4) → p1)) ∨ ((False ∨ (p2 ∧ (p1 → (p1 → p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252569865512518344055276325210 : ((p5 → p3) ∨ (((((False ∨ True) ∧ (False ∨ p4)) ∨ ((False ∨ p1) → ((p2 → p4) → ((p1 ∨ p4) ∨ p4)))) ∧ ((p3 → p5) ∨ True)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164718535520238065675075428168 : (((((p5 ∧ ((p3 ∨ False) ∧ (((p1 ∧ (p1 ∨ p5)) ∧ False) → p3))) → True) → p1) ∨ False) ∨ ((p4 ∨ True) ∨ ((p1 ∨ p5) → (True ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598530620828136236448819842287 : ((((((p2 ∨ p1) → p5) → (((((p1 → p2) ∨ (((True ∨ p1) ∨ p3) → (p5 → p5))) ∨ p2) → (p3 ∨ (p4 → p2))) ∨ p2)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116027008826104018804870422014 : (((p3 ∧ ((p2 ∨ p5) → p5)) → (((p2 ∧ ((p4 ∧ p5) → p4)) ∧ True) ∧ (p5 ∨ ((p2 ∨ p4) ∨ ((p1 → False) ∨ p5))))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184256158844026317353959324153 : ((((((p5 → p5) → (p2 → p3)) ∨ p4) ∧ (True → True)) → False) ∨ (((p2 ∧ p3) ∧ ((p3 → False) → (p4 ∧ (p4 → (p3 → p5))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708001778639844560948617196054 : ((((p1 ∨ ((True → p5) ∧ (p3 → (p5 ∨ p3)))) ∨ ((((True ∧ ((True → (p1 ∧ (p2 ∨ p4))) ∨ (p5 → p5))) ∨ p5) ∧ p2) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656322430125915375198594133979 : ((((((p5 ∨ p1) ∧ ((False → True) ∧ ((False ∨ p2) ∨ (p5 ∧ p2)))) ∨ ((((p4 ∧ p3) ∨ p1) ∧ p1) → (p5 → p2))) ∨ (False ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_264162666334395031609494704360 : (True ∧ (((p3 ∨ (False ∧ (p1 ∨ p4))) ∨ (p4 ∨ True)) ∨ ((p1 ∧ (((p1 ∨ (True → (p1 ∨ True))) → True) ∧ p2)) ∨ (True ∨ (p4 → p2))))) := by
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
theorem thm_5_vars_606628939645572419891813146439 : ((((((p2 ∨ ((((((p2 → p1) ∨ (p5 ∧ False)) → (p5 → True)) ∧ (p4 → p1)) → ((p3 ∨ p3) → p1)) ∨ p5)) → p4) ∧ p2) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52234201255379358730472423857 : (((p2 ∧ ((False ∧ p4) → ((((p1 → p2) ∧ (p2 ∨ p2)) ∨ (True → p1)) ∧ False))) → ((p3 ∧ ((p2 ∧ (p2 ∨ p5)) → p1)) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_60640023511820513441981100262 : ((True ∧ (((p3 ∧ (p3 ∧ (p2 ∧ ((p1 ∧ p2) → (False ∨ (p1 ∨ p1)))))) ∧ ((p4 ∧ p1) ∨ (p3 → p3))) ∨ (p2 ∨ (p1 ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173013245225498858124925982347 : ((p5 ∧ (p3 → (((p1 ∨ p4) ∧ ((((True → p5) ∨ True) → p4) ∨ p3)) ∧ True))) ∨ ((False ∧ p2) → (p1 → (p4 → ((p1 → p4) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336377390148692098728479071296 : (p1 → ((True ∧ (p3 ∨ (((p3 ∧ ((((p2 → p4) → ((p5 ∧ (p2 ∧ (p5 ∨ p4))) ∨ False)) → p4) → False)) ∧ (p4 → p4)) ∧ p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353483716834722575325645926308 : (p4 → (p2 ∨ (((p1 ∧ (False ∧ (((p5 ∧ p4) ∨ (p3 ∨ p3)) ∨ (p5 ∧ p3)))) ∨ ((p2 → p4) → ((p4 ∧ p4) ∨ p5))) ∨ (True ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147092042720537721540048320429 : (((((p4 ∨ p4) ∧ p2) ∧ (True ∨ ((((p3 ∧ p5) ∨ p1) ∨ (p4 ∨ p3)) → (True → (False ∨ p3))))) ∧ False) ∨ ((p5 ∨ p4) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191587440055350255368625856668 : ((p2 ∧ (p3 ∧ ((((p5 ∧ False) ∨ p5) ∨ p5) ∨ True))) ∨ (p4 ∨ ((((p2 ∨ p3) → p2) → p5) ∨ (False ∨ ((False ∧ (p5 ∧ p1)) → p5))))) := by
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
theorem thm_5_vars_618344331583813663267912542573 : (((((p5 ∧ ((False → p3) ∨ p1)) ∨ ((((p3 ∧ (p4 ∨ p4)) → p5) ∧ p5) ∨ (p4 → (True ∧ (p1 → (True ∨ (p3 ∧ True))))))) ∨ p1) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47307695933125007766987301479 : (((((p2 ∨ False) ∨ p3) ∨ ((p1 ∧ (((p5 → ((True → p1) → False)) → ((p1 ∨ (p3 ∧ p2)) ∨ False)) → p2)) → False)) ∨ (p1 ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197336022817283751857980781215 : ((((p5 → p1) → (p5 ∧ (p1 → p3))) → p2) ∨ ((p2 ∧ True) → ((((p2 → (p3 → p2)) ∨ (p3 ∧ False)) → (p1 → p4)) ∨ (True ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45632817063582939682869136788 : (((p4 ∨ ((p2 ∧ (((((p4 ∧ (p3 ∨ p2)) → (p4 → False)) → p5) ∨ True) → (p3 ∨ ((p1 ∧ p4) ∧ p2)))) → (True ∨ p4))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53263092442478729458902884429 : ((((p3 ∨ p5) → (p5 ∧ (((p2 → (p1 ∧ p2)) → True) → p2))) ∨ (True ∨ ((p4 → ((p2 ∨ p1) → (p2 ∧ p4))) ∧ (p4 ∧ p2)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147025811956213228097203224318 : ((((p1 ∨ (p4 ∨ (p1 ∨ ((p2 ∨ ((p1 ∧ p1) → p2)) ∧ (False ∧ p4))))) ∧ ((p1 → True) ∨ False)) ∧ p3) ∨ (p4 ∨ (True ∧ (True → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342982495378709510828253622474 : (p2 → (((p4 ∨ (p1 ∨ p3)) → p1) ∨ (p4 ∨ ((((p2 ∧ (p4 → p4)) → (((p1 ∨ p2) ∧ True) → (p1 ∧ (p4 → True)))) → p1) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p2 ∧ (p4 → p4)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((p1 ∨ p2) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256043526311654245940150372155 : ((True ∨ p4) → ((False ∨ (True ∧ (p1 → ((p5 ∧ (p5 ∨ p1)) ∨ (p1 ∨ (((p2 ∨ (p4 ∧ (True ∧ p3))) ∧ p1) ∧ p4)))))) ∨ (p1 ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768977500256480267967684884442 : (((p5 ∧ (((False → p3) ∨ p2) ∧ ((((p4 → False) → (((((True ∧ p4) ∧ p3) → p4) → False) ∨ p1)) ∨ ((p5 ∨ True) ∧ p4)) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117391546681888198969581198629 : ((p1 ∧ ((((((((((p5 ∨ (p2 → (True ∨ p1))) → p4) ∧ True) ∧ False) ∨ (p2 ∨ p3)) ∨ p1) ∧ True) ∧ p4) ∨ p5) ∨ p1)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168981461866072655508865806679 : ((False → (True ∨ ((((True ∨ p1) ∨ ((p5 ∨ (False → True)) ∧ (True ∧ p2))) → p2) → p2))) → (((p5 → p3) → p2) ∨ ((False ∧ p3) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229341122559760394226357057217 : ((p1 → (True ∧ False)) ∨ ((p3 ∨ (True ∧ p2)) ∨ ((p4 ∧ False) ∨ ((True ∨ ((p2 ∧ p4) ∧ (p5 → (p1 → True)))) ∨ ((p4 ∧ p1) ∧ p4))))) := by
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
theorem thm_5_vars_175529428552256814678952452688 : ((p4 → (((((True ∨ p2) ∧ p1) → p3) → (p2 → True)) ∨ ((p2 → p5) ∧ p4))) → (((p3 ∨ True) ∨ (p5 ∧ ((p5 ∨ True) → p4))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207611934961891147624558422632 : ((((True ∧ (False ∧ p4)) → False) → p5) → ((p3 ∧ (False → True)) → ((((((p2 → p2) ∧ p3) → False) ∨ p2) → (p5 → p4)) ∨ (p5 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : ((True ∧ (False ∧ p4)) → False) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h5
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310232963093864860004080675478 : (p2 ∨ ((((p3 ∨ (p4 → p4)) → ((True ∨ (True ∧ p5)) ∨ p4)) ∨ True) → ((True ∨ p1) ∧ (((p5 → (p2 ∧ (p5 ∧ p4))) ∨ True) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
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
theorem thm_5_vars_65444106835958407641558200155 : ((p3 ∨ ((p4 ∧ p3) ∨ ((((((False ∨ p5) → ((p4 → p2) ∧ ((p3 ∧ p1) → p3))) ∨ False) ∨ p3) → p1) ∨ (p1 ∨ (p3 → p3))))) ∨ p1) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300015990105215822872718224412 : (False ∨ (((p3 → p2) → (p1 → ((p2 → p3) ∨ (p1 ∨ ((p3 ∨ False) → ((((True ∨ p4) ∨ (False ∨ p3)) → p1) ∨ p1)))))) ∧ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147417672950293240354673860804 : ((((p1 ∨ ((p3 ∨ p5) → False)) → ((p5 ∧ (True ∧ ((True → False) ∨ (False → (p5 ∨ p3))))) ∧ p2)) ∨ True) ∨ (((False ∨ p4) → True) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46974760053926559655585157595 : (((((p1 ∨ ((False ∨ (False ∨ p3)) → (((p3 ∨ ((True → True) ∨ p3)) → (p5 → p4)) → (p4 ∧ p2)))) → p4) → p5) ∨ (p1 ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135715184151241339428015027182 : (((p1 ∨ (p3 → ((((True ∧ p4) ∨ False) ∨ p2) ∧ ((p2 ∨ p3) ∧ p1)))) ∧ ((False ∧ ((p2 ∧ p5) → p5)) → p2)) ∨ ((p3 ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49666744949185658052398449166 : (((((False ∨ p2) ∧ p2) → ((p1 → (p1 ∧ (True ∧ (p3 → (p1 ∨ (p1 ∨ True)))))) → ((True ∧ p4) → False))) → ((p5 → p4) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699630199343603276731867277645 : ((((((((True → p2) ∧ p4) ∧ p2) → (False ∧ (True → True))) → False) → ((((p1 ∨ (p3 → (False ∨ p3))) → p1) ∨ p1) ∨ (p3 → True))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



