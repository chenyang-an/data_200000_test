variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306016637880385737142838418927 : (p1 ∨ ((False ∨ (p1 → (p4 ∧ p5))) ∨ (p4 → (((False ∨ (p2 → ((p2 ∨ (False ∨ (p2 ∧ p1))) → True))) ∨ p5) ∧ ((False ∨ False) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143795715061293085951672640173 : (((((p4 ∧ (p4 ∧ ((p3 → False) → (p3 → ((True → (p4 ∨ (p3 → True))) ∨ False))))) → p2) ∨ True) ∨ p3) ∧ (False ∨ ((p5 ∧ p2) → p2))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1664930324428416512147948970 : ((p3 ∧ ((((((((p1 ∨ False) → p2) → p4) ∨ (p4 → p4)) ∨ (p2 ∧ p1)) → p4) ∧ p3) ∧ (p3 → (p3 ∨ p5)))) → (p2 → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310299919018911040046170013052 : (p2 ∨ (((p2 ∧ (((p1 ∨ p2) → False) → p3)) → (p4 ∨ p5)) ∨ ((p5 ∧ p2) ∨ (((p3 ∧ ((False ∧ p4) ∨ p5)) → True) ∨ (p3 ∧ p3))))) := by
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
theorem thm_5_vars_112139706244933803552030640023 : (((p1 ∧ ((((True ∧ p2) → ((p2 → (p2 → ((p2 ∨ ((True → p2) ∧ p1)) → p2))) → (p1 ∧ p5))) ∧ p2) ∧ False)) ∨ p1) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692602853003415940453809906601 : (((((((False → p1) → (p3 → (True ∨ p2))) → p5) ∨ (p3 ∧ (p4 ∧ p1))) ∧ (p4 ∧ ((p2 → ((p3 → False) ∧ (True ∨ True))) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60082994759740707778716185374 : (((p2 ∨ p5) → (((p4 ∧ p4) → (p3 ∧ (p5 ∨ (((False ∧ (p4 ∧ ((p3 ∨ p3) → p1))) → True) ∧ False)))) → (False ∧ (p3 ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_555080105693496961116753565596 : (((p2 ∨ (p1 ∨ ((p1 ∨ (p1 ∧ False)) → ((p3 ∨ (False ∨ (((False → p1) → p1) ∧ (p1 ∧ (((p1 ∨ p1) → p5) ∧ p3))))) ∨ p1)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148277781843642399446012202561 : ((((((((p3 ∧ p4) ∨ p5) → (True ∨ (p2 ∧ p2))) → True) → (p2 ∧ p4)) ∨ p2) → ((p5 ∨ p3) ∨ p4)) ∨ (p4 → ((p5 → True) ∨ p5))) := by
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
theorem thm_5_vars_184505899808537694264060640054 : ((((True → p5) ∨ (((p2 → True) ∧ p4) → p3)) ∨ (p2 ∨ p1)) ∨ ((p3 ∨ (p1 ∨ ((((p4 ∧ p5) → p5) ∨ p2) ∨ p1))) ∨ (p2 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260222295353221389188633487325 : ((p2 → p3) → (((p2 → ((((True ∨ p3) → (p3 → p2)) ∧ ((p3 → p1) ∨ p4)) ∨ p5)) ∨ ((p3 → (p4 ∨ False)) ∨ (p1 → True))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219191830054428796375182163913 : ((False ∨ (p3 ∧ (True → False))) → (((False ∧ (p4 → (p2 → (p5 ∧ (p2 → False))))) ∨ False) ∨ (p3 ∧ (((p4 ∨ p2) ∧ False) ∧ (p5 → p1))))) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778148828920287445932895247237 : (((p1 ∨ ((p5 ∨ False) ∨ (p1 → ((p3 ∨ (p5 ∨ ((False ∨ p3) → (p2 ∨ ((((True ∨ p2) ∧ p4) → p5) ∨ True))))) ∨ (False ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180826673613673468245912620763 : (((p2 ∨ (p5 ∨ p2)) ∧ ((p2 → ((p2 → (p3 ∨ p3)) ∨ p1)) → p2)) → ((p4 ∧ (True ∧ ((p2 ∨ p2) ∨ (True ∨ p1)))) ∨ (True ∨ False))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
theorem thm_5_vars_605799751343413197531964285387 : ((((p4 → (p2 ∨ (((p3 ∨ (p4 → ((p4 → (p3 → True)) → (p1 ∨ (p4 ∧ (True → p4)))))) ∧ (p4 → (p4 ∧ p2))) ∨ False))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689000195606276839064281433799 : (((((((True ∧ ((p4 ∨ (True → True)) ∨ (True ∨ p5))) ∧ (False ∨ p1)) → p2) ∨ False) ∨ ((((p5 → p2) ∨ p5) ∧ p2) ∧ (p1 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153204621999240177215969162869 : ((True ∨ ((p1 ∨ ((p5 ∧ (((False → p3) ∧ ((p2 → p5) ∧ (False ∧ p2))) ∧ p4)) → p1)) ∧ (p2 ∧ p3))) → (p5 → ((p1 ∧ False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h6.left
      let h12 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123545447538776490136602667616 : (((p5 → (True ∧ ((False ∧ (p3 ∧ (p4 → (p4 ∨ (False ∧ (p1 ∧ True)))))) ∧ p2))) ∧ ((p3 → (p2 → p1)) ∨ (p4 ∧ p2))) → (p5 → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120159515177348998627925304044 : ((((p5 ∧ p1) ∧ (False → (((True ∨ p3) ∧ ((False → p3) → ((p3 → p3) → ((p1 → False) ∨ p2)))) → (p4 ∧ p1)))) ∧ p3) → (p4 ∨ p3)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134611903895161211218944081947 : (((((((((False ∧ p3) ∨ p3) → False) ∧ (((False → False) ∧ True) ∨ p1)) ∧ p4) ∨ True) ∨ ((False → p1) ∨ p2)) → p4) ∨ (p5 → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134274181793011457480414141337 : ((((p3 ∨ False) ∧ (((((p5 → True) → (p4 ∧ ((p2 ∨ p3) → (p5 ∧ p1)))) ∧ p3) ∧ (p1 ∧ p5)) ∨ p5)) ∨ p5) ∨ ((p1 ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47536516846015761149518992274 : (((p4 ∨ (p1 ∨ (((p3 ∨ (p3 ∨ p2)) ∧ p5) → ((p5 → p1) ∧ ((p2 → ((False ∧ p4) → p2)) ∧ (False ∨ True)))))) ∨ (p5 ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69194800712731864323679474571 : ((p5 → ((((True → ((p4 ∧ p2) → (p4 ∧ p2))) → p4) ∧ p4) ∧ (p5 ∨ (((p4 ∨ (p2 ∧ ((True → p3) ∨ p2))) → False) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190697320167330263210747894076 : (((((True → (p4 ∨ p1)) ∧ p1) ∨ False) ∧ (p3 ∨ p5)) ∨ ((False → (p1 → False)) → ((False → ((p1 → (p3 ∧ p1)) → (p3 → p4))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181236512706468396255978223744 : ((p3 ∧ ((False → (p2 → (p5 ∨ (p4 ∧ p5)))) → ((p1 → p1) ∧ p5))) → ((p5 ∨ (((True → p3) ∨ (False ∧ p4)) ∧ p5)) ∧ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (False → (p2 → (p5 ∨ (p4 ∧ p5)))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326887863763034217546835078706 : (True → (((False ∧ (((False ∨ (p1 ∨ (((p4 ∧ True) ∨ p3) → (p4 → False)))) ∧ p2) ∨ (((p2 → p1) → p2) ∨ (False → p5)))) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651643793963411593165860123855 : (((((True ∧ p5) ∨ (p1 → (((p2 ∧ p2) ∧ (p3 ∧ (((p5 ∨ (p4 ∨ p1)) ∧ (p5 ∨ (False ∧ p2))) → True))) ∨ p1))) ∧ (p4 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330340213537739509353570824753 : (True → (p1 ∨ (p1 ∨ ((p5 ∧ p1) ∨ ((False ∨ (True ∧ ((p4 ∨ True) → ((True ∨ False) → False)))) → ((p4 ∧ ((p5 ∧ p3) ∧ p3)) ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (p4 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : (True ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172548337217831161989118950989 : ((((p4 ∨ p5) ∨ False) ∨ (True → (p3 ∨ ((False ∨ (p3 → True)) ∨ (p2 ∧ p5))))) ∨ (((p5 ∧ p2) ∧ p1) → ((True → p2) ∨ (p1 → True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114828243246203057688059414766 : (((p4 ∨ (((False ∨ ((p4 → p4) ∨ (p3 ∨ p4))) ∧ (p2 ∧ p2)) ∧ p3)) ∧ ((True → (p3 → p2)) ∧ ((p1 → p2) ∨ p2))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673827749863026185630637693371 : (((((False → True) ∨ (p3 ∧ ((False → p2) → (((p3 → p5) → (p5 ∧ p5)) ∨ (((p5 → p2) → p2) → p3))))) → (p5 ∨ (p2 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136839707146555062939323065002 : (((p2 ∧ p1) ∨ ((((p5 → (p1 → p1)) → ((p2 ∧ True) ∧ ((True → (True ∧ False)) ∧ (p4 ∨ False)))) ∧ p4) ∧ p4)) ∨ ((True ∨ p3) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1406930599880376913017492073 : (((p1 ∨ (p5 ∨ (False ∧ p3))) → (((p2 ∧ (((p1 ∨ (p2 ∧ True)) ∧ p4) ∧ (p4 → False))) ∨ True) ∧ (True ∨ p3))) ∧ (True ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h6
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134762408499942838523681327993 : ((((p3 ∨ p5) → (((p5 ∧ (((True ∨ p4) → (p3 ∧ ((p3 ∧ (False ∨ p5)) ∧ p2))) → False)) ∧ p1) ∧ p1)) → p1) ∨ (p4 → (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111993728723838782868627048282 : ((((p2 ∧ ((p1 ∨ p5) ∨ p5)) ∧ (((True ∨ ((p5 → (True → p2)) ∨ ((True → (p3 ∧ p5)) → p3))) ∧ p2) ∨ False)) ∨ p4) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111238501122158766368817968305 : ((((p4 ∨ p2) ∧ (((False ∨ (p5 → p2)) → ((p3 ∧ ((True ∧ p2) → (p3 ∧ False))) ∨ ((p5 ∨ p5) → p5))) ∧ p3)) ∧ p3) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_581221020259364027156252395526 : (((p4 → (((p2 → p5) ∨ p5) → ((((((p1 → (True ∧ (True → p2))) ∧ (p2 ∨ p1)) → p4) → ((False → p5) ∨ p2)) → p1) → p1))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    have h5 : ((((p1 → (True ∧ (True → p2))) ∧ (p2 ∨ p1)) → p4) → ((False → p5) ∨ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h5
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : ((((p1 → (True ∧ (True → p2))) ∧ (p2 ∨ p1)) → p4) → ((False → p5) ∨ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h10
    -- One of the premise coincides with the conclusion.
    exact h13
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_959802150114086172842702488483 : ((((p3 ∧ p4) ∧ (((((((p4 → p5) → (True ∨ p2)) ∧ (p1 ∨ p4)) ∧ False) → True) → (((p4 → (p5 ∧ p2)) ∨ False) ∨ p3)) → p1)) → p1) ∧ True) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : ((((((p4 → p5) → (True ∨ p2)) ∧ (p1 ∨ p4)) ∧ False) → True) → (((p4 → (p5 ∧ p2)) ∨ False) ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h6
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194019956131875886784574045464 : ((p4 ∨ (True ∧ ((True ∨ (p1 ∧ True)) → (p5 ∧ p3)))) → (((p4 ∨ ((p5 → p4) ∨ (p1 ∧ ((False → p2) ∨ p1)))) ∧ p3) ∨ (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598670481017625769451785957297 : (((((False → (False → True)) → (((((p5 → False) ∧ ((False ∨ (True → p2)) ∨ True)) → ((p3 → (p2 → True)) → p1)) → False) ∧ p3)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192152669114028990115398772827 : ((((((True → False) → (p5 → p4)) ∨ p1) ∧ True) ∧ p4) → (((((False → p3) ∨ p2) ∧ ((p4 ∨ (p1 → p4)) ∧ (p3 → p5))) → p5) ∨ p4)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192144456839256842530828173438 : ((p5 → (True → (((p5 → (p1 ∧ p1)) ∨ p1) → p2))) ∨ ((p5 ∧ ((p2 → ((p5 ∨ True) ∧ (p5 ∧ p4))) ∧ ((False ∧ True) → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638676585525615737413829656189 : (((((((p4 ∧ p2) → (p5 ∨ True)) → p3) → (((p1 ∧ ((p3 ∧ (((False ∧ p1) ∧ p1) ∧ (True ∨ False))) → p4)) ∧ p3) ∧ p3)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325762642034020543140901078547 : (p5 ∨ (p2 ∨ ((p5 ∨ (True ∨ (p3 ∨ p1))) → ((((p2 → p2) ∨ True) ∨ ((p4 ∧ ((p1 ∨ p1) ∨ p2)) ∧ p2)) → (p4 → (p5 ∨ True)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h26 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h26
        case inr h27 =>
          -- Disjunctions on the left can always be decomposed.
          cases h27
          case inl h28 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h29 =>
            -- Disjunctions on the left can always be decomposed.
            cases h29
            case inl h30 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h31 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
      case inr h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h33 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h33
        case inr h34 =>
          -- Disjunctions on the left can always be decomposed.
          cases h34
          case inl h35 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h36 =>
            -- Disjunctions on the left can always be decomposed.
            cases h36
            case inl h37 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h38 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
    case inr h39 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h40 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h40
      case inr h41 =>
        -- Disjunctions on the left can always be decomposed.
        cases h41
        case inl h42 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h43 =>
          -- Disjunctions on the left can always be decomposed.
          cases h43
          case inl h44 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h45 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604305055380072903172887917430 : ((((True → (((p3 → ((p3 → False) ∧ ((p1 → ((p2 ∨ p1) ∨ p4)) ∧ False))) → (True → True)) → ((p3 ∨ True) ∧ (p2 → p5)))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62802814139731657058331456038 : ((p4 ∧ (((((((p5 ∧ (False ∨ p1)) ∨ p4) ∨ p5) ∧ p4) ∧ (p5 ∨ False)) ∧ p3) ∨ (p3 → ((True ∨ ((False ∨ True) ∨ p3)) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345453440008207057767099531483 : (p3 → (((((False ∧ p4) ∨ (False ∨ (((p3 ∨ True) ∨ p2) → ((p5 ∨ (True ∨ (p5 ∨ (p3 ∧ p1)))) → p1)))) ∨ p4) → (p5 ∧ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_26839856232967899683534657195 : (((p1 ∨ p2) ∨ ((p3 ∧ (False → (p4 ∧ p5))) ∨ (p2 → ((p3 ∧ (((p1 → p4) ∧ (((p2 → p1) ∨ p2) ∧ True)) ∧ p5)) ∨ True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_760199651865954095500505631873 : (((p2 ∧ ((False ∨ p2) ∧ (((p5 ∨ p5) ∧ p4) ∧ (p4 ∧ ((((False ∨ ((p5 ∨ p5) ∧ (p1 → p1))) ∧ p3) ∨ (p3 ∨ p2)) → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98803940642975827528572303796 : ((True → ((((False → ((True ∧ ((((p1 → (p2 ∧ p1)) → (p3 ∧ p1)) ∧ (p4 → True)) ∧ p4)) ∧ p1)) ∧ p1) ∧ (p4 ∧ p1)) ∧ True)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8307215892274154058815279276 : ((((((p3 ∧ ((p5 → True) ∨ p4)) ∨ (((((p2 ∨ p4) ∧ (p5 ∨ p1)) → (p5 ∧ False)) ∨ p5) ∨ p1)) → (p4 → p3)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_128137579061106669499782774094 : ((p2 → (((((p5 → p1) → (p4 ∨ p4)) → (True ∨ p5)) ∧ p5) → (((((True ∧ p1) ∨ (p2 ∨ p1)) ∧ p1) ∧ True) ∨ p1))) → (p1 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716437824521547157159341148098 : (((((p5 → True) ∧ (p5 ∨ p1)) ∧ (((False → (False ∧ (True ∧ p4))) → p2) ∨ (((p3 → (p4 ∨ ((True → p3) ∨ p4))) ∧ p4) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117116739831914367739930708278 : (((p3 → p3) → ((((p1 ∧ ((((p1 ∧ p2) ∨ (p3 → p3)) ∨ ((p5 ∨ False) → True)) ∧ p4)) ∧ False) ∧ (p4 → True)) ∨ p5)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238299199239150482822562793913 : ((False ∨ True) ∧ (((p3 → (False ∧ ((False → (p5 → (True ∨ p4))) ∨ True))) → ((p4 → p3) ∨ ((((p4 ∧ p5) ∧ p3) → True) ∨ False))) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137066798056553810532000276475 : (((p3 → p4) → ((p3 → (((p4 → p1) ∨ ((((p2 ∧ p4) ∧ (p2 → p3)) → p2) ∨ p5)) → (False ∧ True))) ∨ True)) ∨ (p1 → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165950241198141502372404299790 : (((p3 ∨ p3) ∧ ((p5 ∨ ((False ∧ p3) ∧ True)) ∨ (p1 ∧ (p2 ∨ (True → (True ∧ p1)))))) ∨ (False ∨ (False → ((p4 ∧ p4) → (p5 ∧ p1))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_770057004443455501886218915789 : (((p5 ∧ (p3 → ((p5 ∨ (((p3 ∨ True) ∧ p1) ∨ False)) ∧ (p2 → (p4 ∧ (((False ∨ (p2 ∨ True)) → (True ∨ p5)) → (p5 ∧ p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309756433013888644530548439829 : (p2 ∨ ((((p1 ∧ p3) ∨ (p4 → p5)) ∨ (((p3 ∨ p1) ∧ p5) → (((True ∧ (p3 ∨ p1)) → p3) ∨ p5))) ∧ (True ∨ (p3 ∧ (p5 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317662029446728379438886035917 : (p4 ∨ ((((True ∧ (((False ∧ (p3 ∧ ((True ∨ p1) ∨ (False → False)))) ∧ ((p2 ∨ False) → p1)) ∨ (False ∧ (p5 ∧ p2)))) → p1) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110773626069323909221558304238 : ((((((True → ((p1 ∧ (p1 ∨ (p3 → (p2 ∨ True)))) ∨ ((True → False) ∨ ((p1 ∨ p2) ∧ p1)))) ∧ p5) ∧ True) ∨ p1) ∧ p4) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350273419235030389712043642520 : (p4 → ((p4 ∧ ((p5 ∧ False) ∧ (((((p3 ∧ p2) ∧ (p1 ∨ p2)) ∨ p1) → (((p4 ∧ p5) ∨ p5) ∨ (p2 → (p1 → p3)))) → p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321008733204569185578682515739 : (p4 ∨ (False ∨ ((((p2 → p5) ∧ True) ∧ ((((p3 → p4) ∨ (False ∧ p5)) ∧ p2) → (False ∧ False))) ∨ (((p3 ∨ p5) → p5) → (True ∨ p4))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_427785605810309093897534926564 : ((((((p4 → (True ∧ (p3 ∨ ((p1 ∨ p2) ∨ (((p4 ∧ True) ∨ (p1 ∨ p4)) ∧ p3))))) ∨ ((False ∧ p3) → p2)) ∨ p2) ∨ (p3 ∧ p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233898693101540259736583365922 : ((p4 ∨ (p4 ∨ p4)) → ((p1 ∧ (((((p3 ∨ ((True ∨ (p1 ∧ False)) → (p3 → p5))) ∨ True) ∨ p5) ∨ ((p2 → p1) ∧ p1)) ∧ False)) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205156184756929152303924862015 : (((p1 ∧ (p4 ∨ p2)) ∧ (p5 ∧ False)) ∨ (p5 → ((p5 ∧ True) ∧ (p5 ∨ (p2 ∨ ((((p2 ∨ (p4 ∧ False)) ∧ (False ∧ p1)) → True) ∧ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211387539026959949819880781696 : (((False → p2) ∨ (p4 → False)) ∧ ((((((p1 ∧ p5) → (p2 ∧ p1)) ∧ (True → p4)) → p5) → (p1 ∨ ((p4 → p2) → p4))) ∨ (True ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305990680161287789251198100633 : (p1 ∨ (((p3 ∧ (p5 ∧ p3)) ∨ False) ∨ (p5 → (((((((p5 → p1) ∨ (False → p5)) → ((p5 ∨ p5) ∨ False)) ∧ p1) ∨ p3) → p4) → True)))) := by
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
theorem thm_5_vars_245730823946528275615649950669 : ((p3 ∧ p2) ∨ ((p1 ∧ ((True ∧ p5) ∧ (p1 ∧ ((p1 → True) → p5)))) ∨ ((p5 ∧ p5) ∨ ((p5 → ((p5 ∨ p3) ∨ p1)) ∨ (False → p2))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111280360114000155015628420383 : ((((p2 ∨ p4) → ((p1 → ((p5 ∧ p5) ∨ ((p2 → ((((False ∨ p3) → p5) → p4) ∨ (p4 → p1))) → False))) → False)) ∧ p1) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592662046779887290118261877633 : (((((p1 → (p4 → (((False ∨ True) → p1) ∧ (p5 ∨ (False ∨ ((((False ∨ p3) ∧ (p5 ∧ p2)) ∧ False) → p4)))))) → (p4 ∧ p5)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625636216061198921094050212846 : ((((p1 → (((p2 → p2) ∧ ((p3 ∧ (True ∧ ((True → ((p4 ∧ (True ∧ p4)) ∨ (p1 → p2))) → p5))) → (p2 ∨ p4))) → p3)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_205626133731956266062566621121 : (((p2 ∧ False) ∨ (p5 ∧ (True → True))) ∨ ((p3 → ((((True ∧ p3) ∨ (p5 ∧ (p3 ∨ True))) ∧ (p1 ∨ (False ∨ p5))) → (p1 ∨ p3))) ∨ p3)) := by
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
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h21 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- False on the left can always be used.
          apply False.elim h23
        case inr h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_551924519004309496727258990 : ((((p5 ∨ p5) ∧ (((((p4 ∧ (((p2 ∨ ((p2 ∧ p4) ∧ True)) ∧ p1) ∨ p1)) ∧ p1) → (True ∧ p5)) → p4) ∧ p1)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47303980792788631146861666158 : ((((p3 → (p3 → p3)) ∧ ((((((p3 ∨ (p5 → p4)) → True) ∨ (p4 ∨ p5)) ∧ (p3 → p1)) ∨ (p3 → p1)) → p3)) ∨ (True ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672675498205226688551863062628 : ((((((p4 ∧ p3) ∨ ((p1 ∧ (((((p3 → True) ∨ (p5 → p2)) → False) ∧ p3) ∧ p3)) → p1)) ∨ (p5 ∨ p2)) → (p2 ∧ (False → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673020223980150021083747900471 : (((((((False ∨ True) ∧ (p2 ∨ (((p1 ∨ p1) ∧ p3) → (True ∨ False)))) ∧ True) → (p4 → (p5 → (False ∧ False)))) → ((True ∧ p2) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322520437562036406276470202988 : (p5 ∨ ((p2 ∧ (((((p1 ∧ p1) ∧ p3) ∧ (((p5 → ((p4 → (p2 ∨ True)) ∨ True)) ∨ p1) → p1)) ∧ (True → (p5 ∨ p5))) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_564887222180710309448446970532 : (((True → (((p1 ∧ ((p5 ∧ p4) ∨ True)) ∧ (p2 ∨ (True → (p1 ∨ (p3 ∨ ((((False ∧ p4) ∧ (p2 ∨ False)) ∧ p3) → p4)))))) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115232716167819143023907108248 : ((((((p2 → False) → True) → (p2 ∨ (p5 ∨ False))) ∨ p3) ∨ (p1 → ((p2 ∨ (p4 → p4)) ∨ ((p3 ∨ True) ∧ (False → p4))))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61656187041929757402299674710 : ((p1 ∧ (p2 ∧ ((p1 ∨ (p1 ∧ (((((p2 → False) ∨ p1) ∧ (p1 ∨ (p1 ∨ p1))) ∨ (True ∧ False)) ∧ False))) ∧ (p1 ∧ (p5 ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716362086116905354513100077511 : (((((p1 ∨ p3) ∧ (True → p2)) ∧ (((((p3 → (False → p1)) ∨ p4) ∧ (p1 ∧ p3)) ∨ ((True ∧ p5) ∨ ((p2 → p4) ∧ False))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231393043064940726246613476740 : (((p1 → False) ∨ True) → (p4 → (((p2 → (True ∧ (p4 ∧ ((((p1 ∨ p5) ∨ p3) ∨ (p5 → (p1 → p3))) ∨ p5)))) ∧ p5) ∨ (p3 ∨ p4)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325901586890806751543257944239 : (p5 ∨ (p4 ∨ (p4 ∨ ((p5 ∧ ((p3 ∧ (True → False)) ∧ (p3 ∨ (((True ∧ p5) → p3) → True)))) ∨ (p1 → ((True ∧ (p5 → p2)) → p1)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54277216713912937815863107154 : (((((p2 → False) → False) ∨ ((p2 ∨ True) → p4)) ∧ (((((((p5 → (p4 ∨ False)) ∨ False) ∧ p4) ∨ p5) → p2) ∨ (p3 ∨ False)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785872935518182655985675420293 : (((p4 ∨ (((True → ((((p2 ∧ p3) → ((True → (p3 → p1)) ∧ (False ∧ (p4 ∧ False)))) ∨ p1) → (p1 → p2))) ∨ p5) ∧ (False ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700092522415693537314659592908 : ((((((True ∧ p3) ∨ p3) → ((p4 ∧ ((p1 ∧ True) → p2)) ∨ False)) → (p5 ∨ (True ∧ ((p2 ∨ (((p3 ∧ p1) → p2) → p3)) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51301208056067578450058948895 : (((False ∨ ((p5 ∧ ((p2 ∧ False) → False)) → ((True → (((p4 ∧ True) ∧ True) ∧ False)) → p1))) ∨ (((p5 → (p1 ∨ p4)) ∨ p3) ∧ p4)) ∨ p2) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193825015161414530379402231898 : ((p5 ∧ (True ∧ ((p5 → ((p4 ∧ p4) ∨ p5)) ∧ p1))) → ((False ∨ ((False → p1) → False)) ∨ (((p5 ∧ (True → (p3 ∨ True))) → p1) ∧ p1))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646193067249673964859729123212 : ((((False → ((False ∧ (False ∧ (False ∨ (p1 ∨ (True → (p2 → (((p1 ∧ (p4 ∧ p4)) ∨ ((p5 → False) ∧ False)) → p4))))))) → True)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219778374511089833449787478900 : ((p2 → ((p3 → p3) → p1)) → (p2 → ((((p2 ∨ p3) → (((p4 ∧ (True → p5)) ∨ ((p1 ∧ (p3 → p4)) → p4)) ∨ True)) ∧ p1) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h8
  -- One of the premise coincides with the conclusion.
  exact h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h13 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h14
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h15 := h12 h13
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205062748397097517019958848456 : (((p2 → (p4 ∨ (p2 ∨ p3))) → p2) ∨ ((((False → (False → (True → (((p1 ∨ p2) ∨ p2) → True)))) ∧ (p4 ∨ p5)) ∨ (True ∧ True)) ∨ p3)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592872893005822037622194661452 : ((((((p2 ∨ (False ∨ p1)) ∧ (p4 ∨ (((p1 ∨ p5) ∧ (p4 → (p2 ∨ (p2 → p4)))) → (p3 ∧ True)))) ∧ (p3 ∨ (p3 ∨ p5))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65021768896334827558228009735 : ((p2 ∨ ((p2 ∨ p5) ∨ (((p5 → (p4 ∧ p4)) ∨ (((((p1 → (True → True)) → p2) ∧ p5) ∨ (p5 ∧ p2)) ∨ p5)) ∨ (p3 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789529101545799213539018000503 : (((p5 ∨ (((True → (p5 ∧ p2)) → ((p2 ∧ (p1 ∨ True)) → p4)) ∨ (p5 ∧ (((p5 ∧ p1) → p4) → (p2 ∧ ((p4 ∨ p2) ∨ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49906541812830608217719001539 : (((((p2 ∨ (False → ((True ∨ ((p5 → (True → p1)) → p2)) ∧ (False ∨ (p2 → p4))))) ∧ True) → p2) ∧ (((p3 → False) ∨ p3) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_917961999005150129347342117169 : (((((p1 ∧ p1) ∨ (((((p4 → p1) → p5) → p1) → ((p3 ∨ p3) → p3)) ∨ p5)) → (((p1 ∧ (p5 → p1)) ∨ p1) ∧ (p2 ∧ p4))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∧ p1) ∨ (((((p4 → p1) → p5) → p1) → ((p3 ∨ p3) → p3)) ∨ p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173483172014133751496757987119 : ((((((p1 → ((False → (p5 → p5)) ∨ p1)) ∨ p1) ∧ (p3 ∧ True)) → False) ∧ p1) → ((p2 ∨ (p2 ∧ (((p3 ∧ False) ∨ p2) ∧ p5))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68179751222188772624885046513 : ((p3 → ((((p2 ∧ (((p2 ∨ p4) → (((p3 → p5) → ((p2 ∧ p1) ∨ (p5 ∧ p5))) ∧ False)) ∨ p3)) ∧ (p4 ∧ p1)) → False) ∨ p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118455290626436513753981239376 : ((p3 ∨ (((p1 → ((p2 → ((False ∧ p1) ∧ p5)) → (((p4 → ((p4 → True) → p5)) ∧ False) ∨ (p3 ∨ True)))) ∨ True) ∨ False)) ∨ (p3 ∨ p1)) := by
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



