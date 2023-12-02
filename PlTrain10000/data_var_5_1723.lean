variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46803406269746851353543530119 : ((((((((p3 ∨ (p4 ∨ False)) ∨ True) ∧ (p5 ∨ p1)) ∨ (((False → (p4 ∧ p3)) ∧ p4) ∨ (False → False))) ∧ p1) ∧ p5) ∨ (p2 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185985462298602319681536245832 : (((False ∨ ((p3 → ((p3 ∨ p4) → False)) ∧ (p3 ∨ False))) ∧ p5) → (p5 ∧ ((((True ∨ (p1 ∨ p1)) ∨ ((True ∨ p2) ∨ p5)) → p2) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56947016453295060991607475837 : (((p1 ∨ (p1 ∨ False)) ∧ (p1 → (p2 ∨ (((((p2 ∨ (p2 ∧ (((p4 ∨ p3) ∧ p1) → p1))) → (p5 ∧ True)) → p2) ∨ p5) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178334579289186695422346726472 : ((((p1 ∨ (False ∨ p1)) ∧ (p4 ∧ (p5 ∨ (p3 → p2)))) ∨ (p5 → p1)) ∨ (False → ((False → p5) → ((p1 ∧ False) → ((p2 ∧ p1) ∨ p2))))) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351912888082095869621343758164 : (p4 → (((p5 ∨ p2) ∧ ((p1 ∨ (p3 ∧ (p1 → False))) ∧ p3)) ∨ (((True ∨ ((p5 ∨ True) → (p1 → True))) → (False ∧ (False ∨ False))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209356441243749430075807340025 : ((False → (True → ((True ∨ p3) → False))) → (p4 → ((p2 ∧ (p4 ∧ (((p2 → p1) → False) ∧ (p3 ∨ False)))) ∨ (False ∨ ((True ∨ p4) → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671239838772799010221985998590 : ((((p4 ∨ ((True → (((p1 ∧ (p4 ∨ False)) ∨ ((p4 → p5) → p4)) ∧ (p4 → p2))) ∨ (p3 → (p4 → True)))) ∨ ((False ∨ p3) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119558762079855749473377503151 : ((p5 → ((((((p3 ∨ (p4 ∧ p3)) ∨ (p3 ∨ p4)) ∨ (p4 ∧ p5)) ∧ p3) ∧ p1) → ((p4 → ((p5 ∧ p3) ∧ False)) ∧ False))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41740334925708488041421598492 : ((((p2 ∨ (p5 → (True → p1))) ∧ ((((((False ∨ p3) → (p2 ∨ p3)) ∧ False) ∨ p1) → (p5 ∨ p2)) ∨ ((True ∨ False) → p2))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774070353024281072288366224366 : (((False ∨ (((p2 → ((p4 ∨ (((p5 ∧ p5) ∨ p3) ∨ p3)) ∨ p2)) ∧ ((((p1 ∨ p3) ∧ (p1 → False)) ∨ p4) ∧ p2)) ∨ (p2 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154303350213614762078079312368 : (((p2 ∧ ((p5 → (p5 → ((p3 → p5) → (((False ∧ p4) ∧ False) ∨ (p3 → True))))) ∨ True)) ∨ True) ∧ (p1 ∨ (p5 → ((p1 → p2) → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692440934385991524181621641741 : ((((((((p1 ∨ p2) → ((p2 ∧ p3) ∧ p4)) → p5) → True) ∧ (p3 ∧ p1)) ∧ (((True ∧ (p5 → (p3 → p1))) ∨ (p1 ∧ True)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198440939826114492556490461370 : ((p5 ∧ (((p3 ∨ False) ∧ (p1 → p2)) ∧ False)) ∨ (((p5 ∨ True) → p5) ∨ ((True → (p5 → (((True → p1) ∧ (p1 ∧ p1)) ∧ p2))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776967523192413413941043168968 : (((p1 ∨ (((p1 → (False ∧ (p5 ∨ ((p3 ∧ ((True → p3) ∧ p2)) → True)))) ∨ (p1 ∧ (((False → p4) → p4) ∧ p4))) ∧ (p1 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39635262311095136679004611295 : (((p3 ∨ ((p3 → (((True → (True ∨ (((True ∨ ((False → p1) ∨ True)) ∨ True) → (True ∨ (p2 ∧ p4))))) ∧ p2) ∨ False)) ∨ True)) ∧ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_48033133493142958891948421048 : ((((((p1 ∧ p2) ∨ (p2 ∨ True)) → ((True ∨ True) ∨ p3)) ∧ (True → ((((True ∨ p4) ∨ (p2 ∨ p5)) → p1) ∧ p4))) → (p3 → p4)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261041804088004524256017812387 : ((p4 → p2) → ((p3 → (p3 → p1)) ∨ ((p2 → ((((False ∧ (True ∧ p3)) ∨ p3) → (True ∧ p4)) ∨ (((p4 ∧ p1) ∨ False) ∨ p2))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307535397638722148679234076798 : (p1 ∨ (True → (p3 → ((((((p3 → p2) ∨ p1) ∧ (((True ∨ p2) ∨ ((p4 ∨ p5) → p5)) ∨ (p5 → p4))) → (p3 ∧ False)) ∨ True) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695592696739463491121247679739 : (((((((p5 ∨ (p5 ∧ p1)) ∧ p5) ∧ p2) ∧ (((p4 ∨ p3) → p5) ∧ p1)) → (((p3 ∨ (p5 ∨ (p1 → p3))) ∧ (p4 ∨ p2)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174423515810638954632184351657 : (((p3 ∧ ((False → ((True ∨ p4) ∧ p4)) → p5)) ∨ (p1 → (False → (True ∧ p4)))) → ((((p3 ∧ p2) ∨ True) → False) ∨ (True ∨ (p2 → p3)))) := by
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
theorem thm_5_vars_117663151198041010740981195141 : ((p3 ∧ ((p2 ∨ ((p5 → p2) ∨ ((p5 ∧ (False ∧ (True ∧ p5))) ∧ ((p2 ∧ (p2 ∧ p2)) ∧ False)))) → ((p3 → p2) → p1))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192799446020433759437882562316 : (((p4 ∨ (True ∧ ((True ∨ p1) ∨ (p2 ∧ True)))) → False) → (p5 ∨ (((p1 ∧ False) ∧ p4) ∨ (p5 → (p2 ∨ ((False ∨ (p4 → p1)) ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ (True ∧ ((True ∨ p1) ∨ (p2 ∧ True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116434641224624071507756350053 : (((p1 → (False ∨ p1)) → ((p4 ∨ False) ∧ (((((p1 ∨ (p4 ∧ p3)) → (p2 ∨ (p2 → (True ∨ p4)))) ∧ p2) ∧ False) → p4))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112320911138617668634503863359 : (((p3 → ((((((p3 → False) ∨ (False ∨ p5)) ∨ p5) ∧ False) ∧ (p5 ∧ p2)) ∧ ((((p3 → p4) ∨ p3) ∧ p2) ∧ True))) ∨ p2) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618268068561991977833599822962 : ((((((p3 ∨ (p3 ∨ p4)) → p4) ∨ (((((p1 → p3) ∧ True) ∧ (p4 → ((p1 ∨ (True ∨ p2)) ∨ (p1 → p3)))) ∨ p5) ∧ p2)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_323493777327824242670260719057 : (p5 ∨ (((True ∧ (p1 ∧ (False → ((False ∧ p4) → ((p3 ∧ p3) ∧ ((p1 ∧ True) → p4)))))) → ((p4 ∨ p3) ∨ True)) ∨ (False ∨ (p3 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134190426148269466554936626372 : (((((p1 → p5) ∨ ((p1 ∨ p4) → (((p5 ∨ p4) ∧ p3) ∧ p2))) → ((p4 ∨ ((p3 → p1) ∨ True)) ∨ p4)) ∨ p3) ∨ ((p4 → p3) → p4)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199083872534620178648831082105 : ((((p4 ∧ ((False → p5) → p5)) → p1) ∧ p1) → (((p4 → (((False → (p3 ∧ p4)) ∧ ((p3 ∧ p3) ∨ p2)) → (p5 ∨ p3))) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300406702567916142200820432841 : (False ∨ ((False ∨ ((p3 ∧ (((False ∨ p5) ∧ True) ∨ ((p4 ∧ False) → p4))) → (p4 ∨ (p1 ∨ ((p2 ∧ p2) → True))))) ∨ (p1 ∧ (p2 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348480205531306745569255734781 : (p3 → (p3 ∧ ((((p4 ∧ (p1 ∧ p1)) ∧ (p4 ∨ False)) ∨ ((p5 → ((((p2 ∧ True) → (p3 ∨ p2)) → True) → p2)) → (False → True))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48349613286341714239586526777 : (((p3 ∨ (((True ∧ p2) ∧ p1) → ((p4 ∧ (p5 → (((p1 ∨ p1) ∨ (p1 ∨ False)) ∧ (p1 ∨ p4)))) ∨ (True ∨ False)))) → (False ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156829047397751253244759685286 : (((True → (((p3 ∨ (((p2 → (True ∧ p5)) → (False ∨ p4)) ∧ p4)) ∨ p1) ∨ (p5 ∨ p2))) ∧ p1) ∨ ((False → p1) ∨ ((p3 ∨ p4) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323317824095975591173534542397 : (p5 ∨ ((((p5 ∨ p3) ∧ ((((p1 → (p1 ∨ p2)) ∧ p1) ∧ p2) ∨ ((p1 ∨ p2) ∨ (p5 ∧ (p2 ∧ True))))) ∧ (p5 ∧ p2)) → (p1 ∨ True))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h3.left
      let h13 := h3.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h3.left
          let h18 := h3.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h3.left
          let h21 := h3.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Conjunctions on the left can always be decomposed.
        let h27 := h3.left
        let h28 := h3.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Conjunctions on the left can always be decomposed.
      let h33 := h31.left
      let h34 := h31.right
      -- Conjunctions on the left can always be decomposed.
      let h35 := h3.left
      let h36 := h3.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h34
    case inr h37 =>
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h38 =>
        -- Disjunctions on the left can always be decomposed.
        cases h38
        case inl h39 =>
          -- Conjunctions on the left can always be decomposed.
          let h40 := h3.left
          let h41 := h3.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h39
        case inr h42 =>
          -- Conjunctions on the left can always be decomposed.
          let h43 := h3.left
          let h44 := h3.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h45 =>
        -- Conjunctions on the left can always be decomposed.
        let h46 := h45.left
        let h47 := h45.right
        -- Conjunctions on the left can always be decomposed.
        let h48 := h47.left
        let h49 := h47.right
        -- Conjunctions on the left can always be decomposed.
        let h50 := h3.left
        let h51 := h3.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190878025510544016368101063707 : ((((False ∨ True) ∧ (p5 → (p1 ∨ p3))) → (p3 ∧ p2)) ∨ (((p3 → (((p5 ∨ (p2 → p4)) → p4) → ((p5 ∧ p4) ∨ False))) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198283510363436874803343268042 : ((False ∧ (p3 ∨ ((p1 → p2) → (p4 → p2)))) ∨ ((p3 → ((False ∧ p1) ∧ p4)) ∨ ((False ∧ ((True ∧ p1) → p1)) → ((p3 ∨ p4) ∨ p4)))) := by
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
theorem thm_5_vars_681506034744360966535538387657 : ((((True → (((p5 ∨ ((p3 ∨ (p3 ∨ p5)) ∨ ((p3 ∧ (False ∧ p2)) ∨ p2))) ∧ (p4 ∧ p3)) ∧ p2)) → ((p3 ∧ (p5 → p4)) ∧ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- One of the premise coincides with the conclusion.
  exact h12
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116078309661025754393116965801 : ((((p5 → p5) ∧ p5) ∧ ((p2 ∨ (((False ∧ ((False → p5) ∧ p5)) ∧ True) → p4)) → ((p2 ∧ (p1 ∧ (p3 ∧ True))) ∧ p1))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118181665486966099382597428300 : ((False ∨ (p4 ∧ ((p3 → ((False → ((p4 ∧ False) ∨ p1)) ∧ (p1 ∧ p1))) ∨ (p5 ∨ ((p1 → p3) ∨ (p4 → (p1 → p4))))))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191731548868662911147406612306 : ((False ∨ (((True ∧ p3) ∨ (False ∧ (p3 ∨ p5))) ∨ True)) ∨ ((p1 ∨ ((((p5 → p3) → p4) ∨ False) ∧ False)) ∨ ((p4 → True) → (True ∧ p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118158900121739536501932313173 : ((False ∨ (((p3 → p5) ∨ False) ∧ (((((p5 → False) → (p2 → p2)) ∧ (p2 → p2)) → ((p1 ∨ (p5 ∨ p5)) ∨ p4)) → p2))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115315431580903202655816436074 : ((((((True → p1) ∧ p4) ∧ p3) → ((p5 ∨ p4) → p4)) → (p1 ∧ ((True ∧ ((True → (p4 ∧ p1)) ∨ (False ∧ p2))) ∧ p4))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114939143335915786130301835903 : ((((p2 → ((p3 ∧ p5) ∨ p5)) ∨ ((True → p5) → (p4 ∨ (p3 → p4)))) → (((((p3 ∧ p4) → True) ∧ p3) ∨ p2) ∨ p1)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184934055588733850507321762010 : (((True → (p4 → False)) ∨ ((p4 ∨ ((p2 ∨ False) ∨ p2)) ∧ p1)) ∨ ((p1 → p4) ∨ (True ∧ ((p4 → ((False ∨ False) → p1)) ∧ (p3 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111837428921770174855372097309 : (((((((p1 ∨ (p2 ∨ ((p1 ∧ True) ∧ p3))) ∨ p3) → p1) → (((p3 ∧ False) → False) ∧ p2)) ∨ (False → (p1 → p4))) ∨ p1) ∨ (p5 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59833982806537819095144478606 : (((p3 ∧ p3) → (((((True ∨ False) ∨ p2) ∧ ((((False → ((p5 ∧ p3) ∧ ((p1 ∧ p1) → p1))) ∨ p1) → p3) ∧ p5)) → False) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619441236431636142981601823973 : (((((True ∨ (p3 ∨ True)) → ((((((p2 ∨ (p5 ∨ p5)) → ((True → p2) ∨ (True → True))) ∨ (p5 ∧ p5)) ∧ True) ∨ False) ∧ False)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180514107286159857813932221578 : (((p3 → ((p2 → ((True ∨ p3) → True)) → False)) ∧ ((p1 ∨ False) → p1)) → ((((True ∧ (True → (p4 → p3))) ∧ p3) ∨ (p1 → p3)) ∨ True)) := by
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
theorem thm_5_vars_774662229522638182152747462247 : (((False ∨ ((((p4 ∧ (p1 ∨ ((p4 ∨ p3) ∧ p4))) → False) ∨ p4) → (((p3 ∧ (p5 ∨ p5)) ∧ True) ∨ (p1 ∨ (p3 → (p3 → p3)))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350118369513660997983745689699 : (p4 → ((((((False ∧ p5) ∨ False) ∧ (True ∧ (((True ∧ p1) ∧ False) ∨ (p4 ∧ True)))) ∨ p3) ∧ (True ∨ ((p3 ∨ True) ∨ (True ∧ p1)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747833610585382285590968047300 : ((((False → p3) → ((((True ∧ p2) ∧ True) → ((((p1 → p1) ∧ (p2 → p3)) ∨ p3) ∨ ((p5 ∨ (True ∧ (p1 → p5))) → p1))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601697874284535258674737694107 : ((((p3 ∧ (p3 → ((p4 ∧ (p1 → p3)) ∧ ((p2 ∧ ((p4 → ((p4 ∨ (((p2 → p5) ∧ p5) → p4)) → p2)) ∨ False)) ∧ True)))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190171391750373627956185897049 : (((p2 ∧ (p3 → ((p1 ∨ (p4 → p3)) → p1))) ∧ False) ∨ (True → (((p3 ∨ p4) ∨ ((False → ((p5 ∧ (p4 ∨ False)) ∨ p2)) ∨ p1)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_156971925491397430897810947038 : ((((((False → p3) ∨ ((p3 → p1) ∧ (p5 ∨ p3))) ∨ True) → ((p4 ∧ p5) → (p3 → p2))) ∨ True) ∨ (p3 → (p4 ∨ ((True → p1) ∧ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58036511698336551231623848482 : (((True ∧ p5) ∧ (((((((True ∨ p4) → p1) → p3) ∨ p3) ∨ p4) ∨ ((p4 ∨ True) ∧ False)) → ((p5 → ((True ∧ p3) ∨ p3)) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646969089863948517673915383630 : ((((p3 → ((p3 ∧ ((((p3 → False) → (((((True → (False → (p1 ∧ p1))) ∧ p3) → p5) ∧ p5) ∧ p2)) → p1) → True)) ∧ False)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158670393821768315903595624090 : ((p2 ∧ ((((p4 → (p3 ∧ p1)) ∨ (((p2 ∨ p1) ∨ ((p1 ∨ False) ∧ p4)) → p2)) → p3) ∨ p3)) ∨ ((((False ∨ False) → True) ∨ p5) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803090291567211109441326844952 : (((p3 → ((False ∧ ((((((True ∨ ((p3 ∨ True) → (False → p4))) ∨ (p5 ∨ p4)) → (False ∧ p3)) → p1) ∨ p5) → (False ∧ p3))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138249237884588015975434917486 : ((p2 → ((p2 ∧ p3) ∨ (True → (((False → False) → (True ∨ True)) → ((((False ∨ p3) → True) ∧ (p3 ∨ p4)) ∧ p3))))) ∨ (p4 ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164152300050579913333062336577 : ((p4 ∨ (((((p1 ∧ (False → (p3 ∧ True))) ∨ ((p5 ∨ p5) ∨ p1)) ∨ p2) → True) ∨ p2)) ∧ (((p3 ∨ (True ∨ p1)) → (True → False)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319470482948946840239129230287 : (p4 ∨ ((p3 ∨ (p5 → (((True ∧ (p2 ∨ p4)) ∨ (p5 ∧ False)) ∨ p5))) ∨ ((((p3 → p1) ∧ (p4 ∧ (True → (p4 ∧ True)))) → p5) ∧ p2))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321353789930660756123504168369 : (p4 ∨ (True → ((((((p1 ∨ (p4 → (p4 → True))) → False) → ((p1 ∨ (True ∨ (True → False))) → p4)) ∨ p5) ∧ ((p2 → False) → True)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p1 ∨ (p4 → (p4 → True))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : (p1 ∨ (p4 → (p4 → True))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h9
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h15 := h13 h14
      -- False on the left can always be used.
      apply False.elim h15
  -- Implications on the right can always be decomposed.
  intro h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136380625194774034396644837241 : ((((p2 → p3) ∧ (p5 ∧ p4)) ∨ (((((p1 ∧ p1) ∨ p4) ∨ (p5 ∨ (False ∨ p5))) ∧ p3) ∨ (p4 → (p3 → True)))) ∨ (p3 ∧ (p4 ∨ p5))) := by
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
theorem thm_5_vars_20101559096188178014591866779 : (((False ∨ (p2 ∨ (((p5 → p4) → (((p3 ∨ p1) → p1) → p1)) ∨ True))) ∧ (((True ∨ (False ∧ (False → (p5 → p3)))) → True) ∨ False)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726819132852673863977022831860 : (((((p1 ∨ p5) → p1) ∨ ((((((p4 ∨ p2) ∨ (False → p1)) → (p3 ∨ p2)) ∧ (p3 ∧ (p5 → p3))) ∨ p5) ∨ ((p1 ∧ False) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56717253784914205176114118691 : ((((True ∨ p4) ∨ p2) ∧ (((p3 ∧ p2) ∧ (((p4 → (((False ∨ p4) ∨ p5) ∧ True)) → True) ∧ False)) ∧ (True ∧ (p1 → (p2 ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601587683799506599090876642235 : ((((p3 ∧ (((False ∧ p4) ∨ (p4 ∧ p3)) ∧ (p1 → (((p3 → True) ∧ (p5 ∨ (p1 ∨ (p2 ∧ (True ∧ (p5 ∧ p3)))))) ∨ p4)))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782972884034120540601608200769 : (((p3 ∨ ((((p3 → False) → (((((True ∧ True) ∧ (p1 ∨ (p2 ∧ ((p3 ∨ p4) ∨ p1)))) → p4) ∨ p5) ∨ p5)) ∨ False) ∨ (p5 → True))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_209443250960857257145239544099 : ((p2 → (p5 ∧ (p3 → (p3 ∨ p2)))) → (((p5 → p2) ∧ ((((((False → p5) → False) ∧ (p4 ∧ p1)) ∨ p5) ∨ (True ∧ p2)) → True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638644000276492990265853137365 : ((((((((False ∧ p5) ∧ True) ∧ p2) ∨ True) → ((((p1 ∧ True) → (p5 ∨ (p3 ∧ True))) ∧ ((p5 → True) → p5)) ∧ (p3 ∨ False))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64895976634174290767294546106 : ((p2 ∨ (((((((((((p4 → (False ∧ True)) ∧ p5) → True) ∨ p1) ∨ p2) ∧ p1) ∨ p4) ∧ p5) → False) → True) → ((p2 ∨ p3) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44541099088090416596831045783 : (((((p4 ∧ p5) → ((p3 ∨ (True → (True → True))) ∨ True)) → (p2 ∨ (((False ∧ p1) ∨ (p5 ∨ (p5 ∨ (p3 ∧ True)))) ∨ p2))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22055543744788083793793053965 : (((((((p1 → p4) → p1) ∨ p5) ∧ p5) ∨ True) ∨ ((((p3 ∧ True) → ((False ∧ p3) ∧ (p4 ∧ p2))) → (p3 ∨ (p5 → True))) ∧ p5)) ∧ True) := by
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
theorem thm_5_vars_307703375785073117684100770549 : (p1 ∨ (p2 → (True ∧ ((p2 → ((((((p2 → p3) ∧ (p5 ∧ (False ∧ p5))) ∨ p1) ∧ p1) ∧ p1) ∨ p2)) ∧ (p2 ∨ (p5 ∨ (p3 ∧ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255786829791502717408240930019 : ((True ∨ False) → ((((p5 ∨ p2) ∨ (False ∧ (p5 → ((p4 ∨ ((True ∨ (p1 ∨ ((p5 → p4) ∧ (p2 ∨ p2)))) ∧ p4)) ∨ p3)))) ∧ True) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657569771067817910748557775636 : (((((p5 → False) ∨ (((False ∧ (True → p2)) ∨ p4) → (((((p4 ∨ (p3 ∧ p1)) ∧ True) ∧ (p5 ∨ p5)) ∨ False) ∧ p4))) ∨ (p4 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192629771972685666451291989644 : (((((p5 ∧ (p2 ∧ (p5 → False))) ∧ True) ∨ True) → p1) → ((((p2 ∧ (p2 → p1)) ∧ ((((p2 ∨ p3) ∨ p2) → p2) → p1)) ∨ False) → p1)) := by
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
    let h6 := h4.left
    let h7 := h4.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184606653008849988859145876162 : (((((p4 ∧ p4) → (True ∧ p1)) ∨ p4) ∧ (p5 ∧ (p1 → p5))) ∨ ((True ∨ True) → ((p2 ∨ (False → ((False → False) ∧ (False → p3)))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683757988702673242547884358853 : ((((((((False ∨ p5) → (p2 ∧ p4)) → ((p4 ∧ (p1 → p5)) ∨ (False ∨ True))) ∨ p3) ∨ p1) ∨ ((True ∧ True) ∧ (p3 ∧ (True → p2)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741577993515606799713297156762 : ((((p5 ∨ p5) ∨ (((((p5 → (p1 ∧ (False ∧ (p5 ∨ False)))) → (p2 ∨ False)) → (p3 ∨ p2)) ∧ (p3 ∧ ((p2 ∧ True) ∧ p3))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139208491144474633041253353593 : (((((p2 ∨ True) → False) ∧ (p2 ∨ (p5 ∧ ((p2 ∧ ((p1 ∨ ((p4 ∨ p5) ∨ p1)) ∨ p4)) → (p5 → p5))))) ∨ p3) → (p2 ∨ (True ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : (p2 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h9
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738708272141295374076638725049 : ((((p2 ∧ p2) ∨ (((p1 → ((((p1 ∨ p1) ∨ p3) ∧ p5) ∨ (False ∧ p5))) → (p2 ∧ ((True ∨ p5) → (False ∧ False)))) ∨ (p3 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118884834908049541096828335452 : ((True → (p1 ∧ (((((((p1 ∧ (p2 → (p4 → True))) ∧ p4) ∧ (p2 → False)) ∨ (p1 ∧ p4)) ∧ (p4 ∧ p3)) ∧ p1) ∨ p3))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185466456933226903403555470920 : ((p1 ∨ (((((True → True) ∧ p4) ∨ p2) → False) ∨ (p3 ∨ p5))) ∨ (((p5 ∧ (p2 ∧ (False → ((p1 ∧ (p2 ∨ False)) ∧ p3)))) ∧ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60442194914301478141460310161 : (((p5 → True) → ((p5 → ((False ∨ (((((True ∨ p2) ∨ p4) ∨ ((True ∨ p5) ∨ (p1 → p4))) ∨ False) → (p4 ∧ p2))) ∧ p3)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255346462154057511800342653123 : ((p5 ∧ True) → (p1 ∨ (((True ∧ (((p5 ∧ ((False ∧ p2) → p3)) ∧ p5) ∨ (p2 → p4))) → p2) ∨ (((p4 → (p3 → p5)) ∨ False) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704189321904004800273060480018 : ((((((False ∨ p1) ∨ ((p3 → p1) → False)) ∨ (p3 ∧ p4)) → (((p3 ∧ p5) → p2) ∨ (p4 ∨ (p4 ∧ (((p1 ∨ p4) → p3) ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59213455924405933018094798187 : (((p1 ∨ p4) ∨ (p2 ∧ (((True → (True ∨ p3)) ∨ ((((p2 ∨ True) ∧ False) ∧ (((True ∨ p4) → (p4 ∧ False)) ∧ p1)) → p3)) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123150957546873560010273955980 : ((((p5 ∨ True) → (((True ∧ ((p4 ∧ (p3 → (p4 ∧ (p3 ∨ (False ∨ p5))))) → p3)) ∧ p4) → p3)) → ((p3 ∨ p2) ∧ True)) → (p2 ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∨ True) → (((True ∧ ((p4 ∧ (p3 → (p4 ∧ (p3 ∨ (False ∨ p5))))) → p3)) ∧ p4) → p3)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h10 : (p4 ∧ (p3 → (p4 ∧ (p3 ∨ (False ∨ p5))))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h6
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h6
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h12 := h8 h10
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h14 : (p4 ∧ (p3 → (p4 ∧ (p3 ∨ (False ∨ p5))))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h6
        -- Implications on the right can always be decomposed.
        intro h15
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h6
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h16 := h8 h14
      -- One of the premise coincides with the conclusion.
      exact h16
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h17 := h1 h2
  -- We need to get the left conjuct of h17 based on <expert-advice>.
  let h18 := h17.left
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h19
  case inr h20 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228224141510781358737252785963 : ((p5 ∧ (p3 ∨ p3)) ∨ (((False ∧ (p3 → ((((p3 ∧ (True → p1)) ∨ p5) ∧ False) ∨ p2))) ∨ (True ∨ (((p3 ∧ p2) ∨ p1) ∨ False))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_91229776033514757156782098808 : (((False ∧ True) ∨ (((p5 → (p3 ∨ (((p5 ∨ p4) → (True ∨ (p1 ∨ (p1 ∧ p4)))) ∨ p1))) → False) ∧ (p3 ∧ (p2 → (p5 ∨ p4))))) → False) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h10 : (p5 → (p3 ∨ (((p5 ∨ p4) → (True ∨ (p1 ∨ (p1 ∧ p4)))) ∨ p1))) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h12 := h6 h10
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610735575283714508267526899971 : ((((((((p4 → (((p2 ∨ True) ∧ p2) → p3)) ∧ ((False ∨ p4) ∨ True)) → (p4 → (p2 ∧ p5))) → (False ∧ (p4 ∨ True))) → p3) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_936796605415469032013914595930 : (((((False ∨ (True → (False ∨ False))) ∨ p5) ∧ ((((p2 ∧ p5) ∧ p1) → ((False ∨ (p1 ∧ (((p1 ∨ p3) ∧ p2) → p5))) ∨ p5)) ∨ True)) → p5) ∧ True) := by
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
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h7 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h8 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h9 := h6 h8
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- False on the left can always be used.
          apply False.elim h11
      case inr h12 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h13 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h14 := h6 h13
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- False on the left can always be used.
          apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h18 =>
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h19 =>
      -- One of the premise coincides with the conclusion.
      exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47197653648380844353362226773 : ((((((False ∨ ((p1 ∨ (True → p4)) → p2)) ∨ (p4 ∧ p2)) ∨ p2) → (p2 ∧ ((p1 → (p3 ∧ (p3 ∧ True))) → p5))) ∨ (p4 ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727573892615090107154084800633 : ((((p5 ∧ (False ∧ p4)) ∨ ((p3 → ((p5 → ((False ∨ (p2 ∧ p1)) → p1)) → True)) → (((p4 ∨ p3) ∨ (p1 ∧ True)) ∨ (p2 ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350639142558857993911912569094 : (p4 → (((p2 ∨ p1) ∧ ((p3 → ((p2 → p5) → p3)) → (((True ∧ p2) → (p1 ∨ ((p5 ∨ False) → (p2 ∧ (p5 ∨ p3))))) ∧ False))) → p2)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : (p3 → ((p2 → p5) → p3)) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h7
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341337960680494712126565591047 : (p2 → (((p4 ∨ ((p4 ∧ p1) → (p1 ∧ (p5 ∨ p3)))) ∧ (((((p1 → ((False → p3) ∨ p3)) → p3) → p1) ∨ (True → p2)) → p3)) → p3)) := by
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
    have h6 : ((((p1 → ((False → p3) ∨ p3)) → p3) → p1) ∨ (True → p2)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h6
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : ((((p1 → ((False → p3) ∨ p3)) → p3) → p1) ∨ (True → p2)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h12 := h4 h10
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596022483744392676496273333158 : ((((((p1 ∨ ((p4 ∨ p5) → (False ∨ (True ∨ p5)))) ∨ p3) → (((p4 → False) ∧ ((p3 → p5) → (False ∨ (p3 ∧ False)))) ∧ p5)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357070978211340467721873967004 : (p5 → (((True ∧ True) ∨ p3) → (((False ∨ ((p2 ∧ (((p4 ∨ ((p1 → p2) ∧ (p3 ∧ p1))) ∨ False) → (p4 ∧ True))) ∨ p5)) ∧ p5) ∨ p4))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155043088229661897094552696263 : ((((p5 ∧ (False → p3)) → ((False ∧ p3) ∧ (p5 ∧ (p1 ∨ p3)))) ∨ (((True ∨ p2) ∨ True) ∨ p5)) ∧ (p2 → (p3 → ((p1 ∧ True) ∨ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303969624478994833061517463537 : (p1 ∨ (((p4 ∧ (False → False)) ∨ ((p5 ∧ ((p3 ∨ (p2 → False)) ∨ (p5 → (((p1 ∨ (True → p3)) ∨ p4) → (p3 ∧ p1))))) ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



