variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40726797670763551425381169615 : ((((((p4 ∨ p2) ∨ ((p2 ∨ p5) ∨ False)) → (p2 → ((((p5 ∧ (p3 ∨ p5)) ∨ (p5 → (p1 ∨ p4))) → p4) → p5))) → False) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42934615353150282115002948908 : (((p4 → ((p5 → (((p1 ∧ True) ∧ (((p3 → p2) ∧ (p5 ∧ (p2 → (p3 → p3)))) ∨ p5)) ∧ p4)) → ((False ∧ p5) ∨ False))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747964940187096919954589550929 : ((((p1 → True) → ((p1 → (True ∨ ((p4 ∧ p3) ∧ (p5 ∧ ((p5 ∧ p1) ∨ True))))) → (p2 ∧ ((p4 ∨ (p1 ∧ False)) ∧ (False ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66665720809183803853218059478 : ((True → ((p5 ∨ ((p5 ∧ (p1 → p2)) ∧ p2)) ∧ ((p2 ∧ (p3 ∨ (p4 ∨ (((p2 ∧ True) → ((p2 → p5) ∧ p4)) ∨ p5)))) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197691114232922981529862259334 : (((p2 ∨ ((p1 → p5) ∨ p2)) → (p3 ∧ p5)) ∨ (((((True ∧ p5) ∧ (p2 ∧ (p5 → (p1 ∧ False)))) ∧ ((p4 ∧ p2) ∧ True)) ∧ p1) → False)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h10 := h7.left
  let h11 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h5.left
  let h13 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h16 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h17 := h11 h16
  -- We need to get the right conjuct of h17 based on <expert-advice>.
  let h18 := h17.right
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172917396694928777468125018238 : ((p2 ∧ (p3 ∧ ((p1 ∧ (p5 → ((p5 ∧ p5) → p1))) ∨ ((p3 → p4) ∧ p3)))) ∨ (((p1 ∧ False) → ((p2 ∨ (False → p2)) → False)) ∨ p5)) := by
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
    let h4 := h1.left
    let h5 := h1.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41053105553517014902967838417 : (((((True → p1) ∧ (((True ∨ ((p2 ∨ False) → ((False → (p4 ∧ p4)) ∨ (p5 ∨ (p4 ∨ p2))))) → p5) → p5)) → (False ∧ False)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49193273601686132998404311490 : ((((p3 ∧ (p4 ∧ False)) ∧ (p1 ∧ ((((((p4 ∧ p3) → False) ∨ True) ∨ ((p4 ∨ p1) ∨ True)) → p5) ∧ True))) ∨ ((p3 → p4) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112083774927282775099935399006 : ((((p1 ∨ p1) ∨ (p3 → (True → (((p4 ∧ (False ∨ (p1 → ((p3 ∨ (p2 → (p4 ∧ False))) ∨ p1)))) ∧ p4) ∨ p3)))) ∨ True) ∨ (p4 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339783988722352811512477515270 : (p1 → (p5 ∨ (((((True → p4) ∧ ((p1 ∨ (p1 ∧ p5)) → ((p1 → False) ∧ p2))) → (p5 ∧ (((p3 → p1) → False) ∨ p5))) ∨ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632262510014093559496191737406 : (((((p1 ∧ (p1 ∧ (p1 ∨ (((True → False) ∨ False) ∧ (((p3 → (p2 ∧ p5)) ∧ p3) ∨ ((p5 ∧ False) ∧ (p1 ∨ p4))))))) → False) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41300281731480694451108280862 : ((((p4 ∨ ((p3 → (p2 ∧ ((p4 → ((p5 ∨ (p3 → p5)) → p4)) ∨ p3))) → (p3 → True))) → (((p2 ∨ p4) ∧ p4) → p5)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178618427505031697322361501356 : ((((p5 ∨ ((p1 ∧ p4) ∧ p4)) ∧ True) → ((True → p1) ∧ (p2 ∨ False))) ∨ ((((p3 → True) → (True ∨ p5)) ∧ ((False → p4) ∨ p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790022681379577258300447015025 : (((p5 ∨ ((p4 ∧ p1) ∨ ((((((True ∨ False) ∧ ((((p4 ∨ True) → p1) → p1) → p3)) → p4) ∧ p1) ∨ p5) ∧ (True ∨ (False ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178306229733283069123458640457 : (((((p1 ∨ False) → ((True → (p5 → p4)) → p3)) ∧ p4) ∨ (p4 ∧ False)) ∨ ((False → (True ∧ p3)) ∧ (((True → False) ∧ False) ∨ (True ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615839464637809866862115034964 : ((((((((p5 → (False ∨ p3)) → (p1 ∧ p3)) → False) ∧ (p4 ∧ (False → p2))) ∨ (((p5 → True) ∨ p4) ∨ (p1 ∧ (p2 → False)))) ∨ False) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227266198114300075898085328298 : (((p1 → p1) → False) ∨ (((p1 → True) ∨ p5) → ((p2 → (p4 ∧ False)) ∨ (((p1 ∨ True) ∨ (p5 → p4)) ∨ ((p3 ∧ (p5 ∧ False)) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
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
theorem thm_5_vars_787714335069634062300302383935 : (((p4 ∨ (p5 ∨ ((p3 ∧ (p2 → ((p2 → (True ∨ p3)) → p2))) → (((p3 ∨ ((p1 → p3) → False)) ∧ ((p3 → p3) ∧ p3)) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301884723746182100066233764437 : (False ∨ ((p5 → p4) ∨ (p1 ∨ (p5 → ((p2 ∧ ((p4 → ((p3 ∧ (p4 ∨ p1)) → ((False ∧ True) → False))) ∧ ((False ∨ p2) ∧ p1))) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704509153764681066631659474729 : (((((p1 ∨ True) ∧ (p3 ∨ ((False → p1) ∧ (True → p3)))) → ((p4 ∧ ((((False ∨ p5) → (p3 ∨ (True ∧ True))) ∨ p3) ∧ p4)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714617455647632165943769312704 : (((((p1 → p4) ∨ (p4 ∨ (p3 ∨ p4))) → (p3 → (p5 ∨ ((((False → ((p5 → ((True ∨ False) ∧ p5)) ∧ False)) ∨ False) ∨ p3) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254062907432140965882539181684 : ((p2 ∧ True) → ((p4 ∨ p2) → (((p2 ∨ ((p4 ∨ (((p5 → False) → (p1 → p1)) → p5)) ∧ ((p1 → (p2 → p2)) ∨ p5))) → p5) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622449282424967347053907803285 : ((((p3 ∧ ((p3 ∨ p2) ∨ (p3 ∧ (((p4 ∨ ((((p1 → p5) ∧ p2) ∧ p4) ∨ False)) ∨ (((p5 → True) ∧ False) ∨ p2)) ∧ p2)))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66308681180785894936536401335 : ((p5 ∨ ((p3 ∨ p5) → (p5 ∨ (((((True ∨ p4) ∨ (p4 ∧ p4)) → (False ∨ True)) → (p5 ∨ ((True ∧ p2) ∧ p4))) ∧ (p3 → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797715852687290898482026061177 : (((p1 → ((False ∨ (((p3 → False) → (p4 ∨ (False → (p5 ∧ (p1 ∧ ((p1 ∧ p4) ∧ True)))))) ∧ (p3 → (p4 → (p1 ∨ False))))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134283444981703766308920525998 : ((((p4 ∧ p4) ∨ (((True → p5) ∨ ((p5 ∨ p1) ∨ ((p2 → p4) → (False ∧ p4)))) → (p4 ∨ (True ∧ False)))) ∨ p2) ∨ ((p3 ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121359454410876862369108086870 : (((((False ∨ (((p2 → p3) ∧ (p1 ∧ (p1 ∨ ((p1 ∧ p5) ∧ (p2 ∧ ((p4 ∨ p5) → p1)))))) ∨ True)) ∧ True) ∨ p2) → p2) → (p5 → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((False ∨ (((p2 → p3) ∧ (p1 ∧ (p1 ∨ ((p1 ∧ p5) ∧ (p2 ∧ ((p4 ∨ p5) → p1)))))) ∨ True)) ∧ True) ∨ p2) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43443132660994221979804845991 : ((((((False → p2) → p1) ∨ ((p2 ∨ (p4 ∧ ((p2 ∧ (p4 ∨ (p4 ∨ ((p3 ∨ (p2 → False)) ∧ p5)))) → p5))) ∨ p3)) ∨ False) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227119957652636058792131822294 : (((p4 ∨ p3) → False) ∨ ((p3 ∧ ((p2 ∨ p4) ∧ True)) ∨ ((((((False → (((False ∧ False) → False) ∧ p1)) → p1) ∧ False) ∧ p3) ∧ True) → p3))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156900994076996053157106033197 : ((((p5 ∨ ((p5 → p1) ∧ ((((True ∨ (p4 → True)) ∧ p2) ∨ p2) ∨ (p5 ∨ p1)))) ∨ p3) ∨ p4) ∨ (True ∨ ((p2 ∧ p1) ∨ (p2 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599904737577053513949289727278 : (((((p3 ∧ p2) → ((p1 → ((p1 ∨ p1) ∨ ((p3 → p4) ∨ p2))) ∧ ((p1 ∨ (p1 → (((False ∨ p5) → p2) → p5))) ∧ p3))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64791006181797501119341193019 : ((p2 ∨ ((((p5 ∨ (p1 ∧ (p5 ∨ p3))) ∧ (p1 → p2)) ∨ ((((((p5 → (p5 ∨ p4)) → p1) → p5) → p5) → p5) ∧ p5)) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647662848535412535461190605372 : ((((p5 → (((False ∨ p2) ∨ (p5 → p1)) → ((False ∧ ((p2 ∨ (((p5 → (False ∨ p3)) → False) ∧ p4)) ∧ (True → p1))) ∨ True))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148943122767189168590289561749 : (((p5 ∨ ((p3 → p3) → p1)) → (p1 → ((p5 → (((p3 ∨ ((p2 ∧ p4) → p5)) ∨ p2) ∨ p1)) ∧ p5))) ∨ ((p3 ∧ False) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40357973830645283187511993869 : ((((((p4 → (True ∧ (True ∨ (((((p3 ∨ p5) → False) ∧ False) ∨ ((p4 → p1) ∨ False)) ∧ True)))) → (p5 → False)) → p3) ∨ p1) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201131742209890870788000553038 : ((False → (((p1 ∨ (p5 → p1)) → p4) ∧ p3)) → ((p2 ∨ ((p5 → ((p5 ∧ (((p3 → False) ∨ True) → False)) → p2)) ∨ (p1 ∧ True))) ∨ p5)) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((p3 → False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199000709030940860287667246835 : ((((((p3 ∨ True) ∨ p4) ∧ p4) ∧ p3) ∧ True) → (p2 ∨ (((p1 → p5) → (p2 → (p2 → False))) → ((False ∧ (p4 ∧ (p2 ∧ False))) ∨ p3)))) := by
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
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166085932376994263117923438467 : (((p4 ∨ p1) → ((((((p5 ∨ p3) ∧ p2) → (p5 ∧ (p5 → p3))) → p2) ∨ p4) ∧ False)) ∨ (p5 → ((((p1 ∨ p1) ∨ p5) ∨ True) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218543147031756147579710903615 : (((p5 ∨ p4) → (True → False)) → ((p2 → (p1 → (p3 ∨ (((p2 ∨ p5) ∨ p1) ∧ p2)))) ∧ ((p3 ∧ p5) ∨ (p1 ∨ (p4 → (p4 → p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p5 ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55158855074450751347742417399 : ((((p2 ∧ ((False ∨ p5) ∨ p4)) ∨ p1) ∨ ((p3 ∧ (p5 → (False ∨ False))) ∨ ((p5 ∧ p3) → (p4 ∧ ((p1 ∨ (p4 → p1)) → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199499946690175305281946118525 : (((False → (p4 ∨ ((False ∨ p5) → p4))) ∨ False) → ((True ∧ ((p4 → ((p2 ∧ p5) ∨ True)) ∧ (p1 ∧ ((p3 → (True ∧ p5)) → p5)))) ∨ True)) := by
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
theorem thm_5_vars_161183620181248214475658631022 : (((p1 ∨ p2) ∨ ((p4 ∨ (p1 ∨ (((p3 ∨ p3) ∨ (p2 ∧ p2)) → (True → True)))) ∧ (p1 → p5))) → ((p4 ∨ p2) ∨ (False → (p4 ∨ p4)))) := by
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- False on the left can always be used.
        apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186820992570077989744008769855 : (((((p3 ∨ p4) ∨ False) ∧ p1) ∨ ((p4 → p4) ∧ (True → p3))) → ((p2 → (((p4 → p1) → (p3 ∧ ((p3 ∨ True) → p3))) → p3)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- Implications on the right can always be decomposed.
        intro h8
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h17 := h13 h16
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113498637996109329151433037174 : ((((((p1 ∧ p1) → ((((p5 ∨ ((p4 ∨ p1) → p1)) ∨ p3) → p3) ∧ p3)) ∧ True) → ((p2 ∧ p2) → False)) ∨ (True ∧ True)) ∨ (p4 → p3)) := by
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
theorem thm_5_vars_672893664984804178263338193070 : (((((((p5 ∨ ((True → (((p1 → False) → p5) ∧ (p5 ∧ True))) ∧ p2)) ∧ True) ∧ p2) → (p2 ∨ (p3 ∨ p2))) → (p2 ∧ (False → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232715427495903839348207144017 : ((p1 ∧ (p4 ∨ p1)) → ((False ∧ ((((True → p2) ∨ (((p3 ∨ (p5 ∧ p1)) → p2) ∨ p2)) ∧ ((p1 → p2) ∨ p4)) ∨ (p3 ∨ p1))) ∨ p1)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664400936916352867207898020267 : ((((p3 ∨ ((((p3 → p4) ∨ (p4 → (p4 ∨ (False ∨ p1)))) → p3) → (p1 ∧ (p4 ∧ ((p5 → False) → (False ∨ False)))))) → (p3 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755108278671045832810067288995 : (((False ∧ (p1 → (p2 ∧ (((p1 ∨ (True ∨ ((p5 ∧ p4) ∨ (p3 ∧ p5)))) → p2) → ((p1 ∧ (p3 ∧ ((p3 → True) → p1))) ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52677487561348977757080744476 : (((p2 ∨ ((p4 ∧ ((p5 ∨ p1) ∨ ((p2 → True) → p4))) ∨ (True ∧ False))) ∨ (((False → ((p2 ∧ True) ∨ p2)) ∨ p5) → (p5 → p5))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265525620143142597446291728384 : (True ∧ (False ∨ (((p3 ∧ ((p3 ∨ ((False → p4) ∧ p3)) ∨ ((p5 → ((p1 ∨ (p3 ∨ False)) ∧ (False → True))) → p2))) → p1) → (p4 → p4)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656674701925668234606201874659 : ((((((p5 ∨ ((True → p5) ∧ p2)) ∨ False) ∧ (p4 ∧ (((True → p2) ∨ True) ∧ (False → ((p3 ∧ (p3 ∨ False)) ∨ False))))) ∨ (True → True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_204562408888975247008954669315 : ((((p1 ∧ p5) ∧ (p1 ∧ p3)) ∨ p3) ∨ (((((p4 ∨ (True → p2)) ∨ True) → (p2 → p3)) ∨ (False ∧ (p4 ∨ p3))) ∨ ((False ∧ p5) → p1))) := by
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
theorem thm_5_vars_936545381837433445153213799214 : (((((True ∧ (True → (True → p4))) ∧ True) ∧ ((True → p5) ∨ (((True → p5) ∨ (p4 ∨ False)) ∨ (p4 ∨ ((p3 ∧ True) → (True ∧ p2)))))) → p4) ∧ True) := by
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
  cases h3
  case inl h8 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h17 := h7 h16
        -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
        have h18 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h17, we can now drive its conclusion.
        let h19 := h17 h18
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h22 =>
          -- False on the left can always be used.
          apply False.elim h22
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h25 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h26 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h27 := h7 h26
        -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
        have h28 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h27, we can now drive its conclusion.
        let h29 := h27 h28
        -- One of the premise coincides with the conclusion.
        exact h29
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53234864754774119031581116528 : ((((True ∧ (p1 → p2)) ∧ (True ∧ (p1 ∨ (p4 → (p1 ∧ p1))))) ∨ (((p4 ∨ p4) ∨ ((((p4 → p2) → p5) ∨ False) → False)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172592181430732868076483285241 : ((((False ∨ p1) → p3) → ((((p1 → ((p1 ∧ p3) ∧ p5)) ∨ p4) ∧ p5) → p4)) ∨ (True ∨ (p2 ∨ ((p4 ∨ p2) ∨ (p4 → (True ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213619413915941131698372287924 : ((((p2 ∧ False) ∨ p1) ∨ p2) ∨ (((p2 → False) → (p4 ∧ (True ∨ ((((p4 ∧ ((p4 ∧ p3) ∧ p3)) ∧ p1) ∧ True) ∧ p4)))) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233623818496766724288348230180 : ((p2 ∨ (p4 ∧ p4)) → (p4 → ((p2 ∧ p4) ∨ (((p4 ∧ ((p4 → p1) → p2)) ∧ (False ∨ p3)) ∨ (((p2 ∨ p3) ∨ p4) → (p4 ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661976450195709804241908474366 : (((((True → (p3 ∧ ((((True ∨ p2) ∨ p5) → (p5 → (p5 → p4))) → p1))) ∨ ((True ∨ False) ∨ ((p5 ∧ p3) → True))) → (p3 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53872381067930763441861578198 : ((((True ∧ p4) ∨ (((p5 ∨ (p4 → p1)) ∨ False) ∧ True)) ∨ ((((False ∧ (False → p2)) → False) ∨ p4) → (p5 ∨ (False ∧ (True ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190040375148681328631960836901 : ((((((p5 ∧ False) → False) ∧ (p2 ∨ p5)) ∨ p3) ∧ p2) ∨ (((((p1 ∨ ((p1 → False) → p4)) ∨ p3) → ((p4 ∧ True) ∧ p1)) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170282172945362897485603859363 : ((((True → False) → (p1 ∨ p3)) ∧ ((((p1 → (p2 → p3)) ∨ p3) ∨ p2) ∨ True)) ∧ (p5 → (((p2 → p2) ∨ True) → ((p2 → p4) → p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354682913854055678953786125709 : (p5 → ((((p1 ∨ False) ∧ ((True ∧ p1) ∧ (((True ∨ (False ∨ (p1 ∨ False))) ∧ p2) → (((p3 ∨ p1) ∧ p2) ∧ True)))) ∧ (p3 → p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184988314389799208429132961532 : (((False ∧ True) ∧ (((False → (True → (p4 ∧ p1))) → p4) ∨ False)) ∨ ((p1 ∧ ((p5 ∧ True) ∨ p2)) → ((((p3 ∨ p4) → p2) ∧ p4) → p2))) := by
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
  let h5 := h1.left
  let h6 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : (p3 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327027008048739651873414224991 : (True → (((((p5 ∨ ((False ∨ p4) → p5)) ∧ (p3 ∧ False)) ∨ (p2 ∧ p4)) ∨ ((True → ((True → True) ∨ (True ∧ (p4 ∨ True)))) ∨ p2)) ∨ p1)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648204293491949045757255982856 : (((((p4 ∧ ((p1 → p5) ∧ ((p1 ∨ ((p1 ∨ p3) → (((((p1 → p5) → p2) ∨ p1) ∨ p4) ∨ p4))) ∨ p4))) ∧ p1) ∧ (p3 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61358704214778480573138336044 : ((p1 ∧ ((True ∧ ((p4 ∧ ((((((True ∨ True) → p5) ∧ (p3 ∧ (False → (p4 ∧ p1)))) ∧ p3) ∧ p4) ∧ p5)) ∧ (p5 → p2))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207002234963170741631555989241 : ((((True ∧ p4) ∨ (p3 → p1)) ∧ p5) → ((((((p5 ∨ p4) → (p1 ∨ (((p4 ∧ True) ∨ (False ∧ True)) → False))) → p3) ∨ p4) ∨ True) ∨ p4)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675855167376644801797691505828 : ((((((p3 → p4) ∧ (p1 ∧ (((False → p3) → (False ∨ False)) ∧ p2))) ∨ (False → (p4 ∨ (True → p3)))) ∧ ((False ∧ (True → p5)) ∨ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196873631866610967719967811594 : (((p5 ∨ ((p5 → p5) → (p1 → p5))) ∧ True) ∨ ((p5 ∧ (p2 ∧ p4)) → (((False ∨ p4) ∧ p3) ∨ (p1 ∨ (p3 ∨ ((p3 ∧ p5) → p4)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42344902096001286435264709350 : (((p3 ∧ (((p4 → p5) ∧ (False ∨ ((p4 → p1) → (p1 ∧ (p2 ∨ ((p4 ∧ p1) → True)))))) ∨ ((p3 ∧ (p2 → p5)) ∨ p5))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625629039630671239401055461049 : ((((p1 → (((((True → False) → ((True ∧ (p1 ∧ (((p3 ∨ False) ∨ p1) ∨ p3))) ∨ p3)) ∧ p1) ∨ (p5 → (p1 ∧ True))) → p3)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319562060717576616718315650339 : (p4 ∨ ((p2 → ((p4 ∧ p3) ∨ (((p5 → True) → p5) ∨ True))) ∨ (True → ((p1 ∧ (p2 → (((False → p4) → (p4 → p5)) ∧ p1))) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_215332244175643277692551073419 : ((p1 ∧ (p2 ∨ (p5 ∧ p4))) ∨ (p3 → ((p2 → (p3 → (((p1 ∧ ((p4 → p2) ∧ p1)) ∨ p4) ∨ (p3 ∧ (p1 → p2))))) ∨ (False ∨ p5)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47185693814113577081796892364 : ((((((True ∧ ((p1 ∧ p3) → p3)) ∧ (p3 ∨ p2)) ∨ (p4 ∧ False)) ∧ ((p4 ∧ p5) ∧ (p3 → ((p3 ∨ p5) ∨ False)))) ∨ (False ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75635053693467281587915916418 : ((((((((((p5 ∧ p4) ∨ ((p2 ∧ (p4 → False)) ∧ (p2 → (False → p1)))) ∧ False) ∧ True) ∨ (p2 → False)) ∧ p3) ∧ p1) ∨ True) → False) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((((p5 ∧ p4) ∨ ((p2 ∧ (p4 → False)) ∧ (p2 → (False → p1)))) ∧ False) ∧ True) ∨ (p2 → False)) ∧ p3) ∧ p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689558226632179605716388560740 : ((((((True ∧ (p3 ∧ (True → p3))) → (False → p4)) → (p4 ∧ (True ∧ (p5 ∧ p4)))) ∨ (((p1 → (False ∧ p5)) → (p2 ∧ p5)) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_39574991024727997724089417430 : (((p1 ∨ ((False ∨ p4) ∧ ((((((((p1 ∧ False) ∧ False) → p2) ∨ (p3 → p4)) ∧ False) ∧ (p3 ∧ (True ∨ False))) ∨ False) ∧ p2))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159631182447901972003245212552 : ((((((False ∨ (p4 ∨ ((False ∧ p3) ∧ ((True ∨ (p1 → p2)) ∧ p3)))) → p1) → p3) ∨ p3) ∨ p3) → (p2 → (False ∨ (p1 → (p4 ∨ p3))))) := by
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
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h6 : ((False ∨ (p4 ∨ ((False ∧ p3) ∧ ((True ∨ (p1 → p2)) ∧ p3)))) → p1) := by
        -- Implications on the right can always be decomposed.
        intro h7
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- False on the left can always be used.
          apply False.elim h8
        case inr h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- One of the premise coincides with the conclusion.
            exact h5
          case inr h11 =>
            -- Conjunctions on the left can always be decomposed.
            let h12 := h11.left
            let h13 := h11.right
            -- Conjunctions on the left can always be decomposed.
            let h14 := h12.left
            let h15 := h12.right
            -- False on the left can always be used.
            apply False.elim h14
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h16 := h4 h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h20
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263074769496340018973438314169 : (True ∧ (((p4 ∨ ((p2 ∧ ((p3 ∨ (p4 → True)) → ((False → p3) → ((p1 ∧ True) → (p4 ∨ p1))))) ∧ (p1 → p4))) ∧ p5) ∨ (True ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800459498006356310668137542125 : (((p2 → ((p5 → (((((p4 ∨ p1) → (p1 ∧ p2)) ∧ p3) ∨ ((p2 ∧ ((p3 → False) ∨ (p2 ∧ (p1 → p5)))) → False)) → p4)) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_44159345169512161716740540641 : (((((p1 ∨ ((((p5 ∧ False) → False) → p5) ∧ (p2 ∨ (p1 ∨ (p3 → p3))))) ∧ ((p1 ∨ p5) ∧ p4)) → ((p1 → True) ∨ p1)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187460504044676834727715685117 : ((True ∨ ((False → (p1 ∨ True)) → (((p2 ∨ p5) ∨ False) → False))) → (True ∧ ((p3 ∨ (((True → p1) ∨ p2) → (p3 ∨ (True → p4)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_192297095794492042394720952797 : ((((False → p3) → ((p4 → p2) ∧ (p5 ∨ p1))) ∧ p4) → (((p3 ∧ False) ∧ (((True ∧ False) → ((p1 → p3) ∨ p5)) → p1)) ∨ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193721159215859144144695769245 : ((p2 ∧ ((True ∧ (p2 → p3)) ∧ (p3 ∧ (p1 ∧ True)))) → (((True ∨ ((False → (True ∨ p4)) ∨ True)) → ((p4 ∧ p5) ∧ False)) → (False ∨ False))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h9 := h6.left
  let h10 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h13 : (True ∨ ((False → (True ∨ p4)) ∨ True)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h14 := h2 h13
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148517268979440742100179417440 : ((((True → ((True ∧ (p3 ∨ (p4 ∨ (p2 → p2)))) ∧ True)) ∨ p1) → ((p2 ∧ p1) ∨ (p1 → (False ∨ p3)))) ∨ ((p5 ∨ (False → p4)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190321719605390138981068198744 : (((((p2 → p1) ∧ (p4 ∧ False)) ∨ (p2 ∨ p5)) ∨ p3) ∨ ((((p4 → p2) → ((p4 → ((p2 ∧ True) ∧ (p1 ∧ p3))) ∨ p1)) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234143699728779779891697076579 : ((True → (True → p1)) → ((False ∧ (((p3 ∧ (False ∨ (p4 → (p5 → (True ∧ ((p5 ∨ False) ∨ (True → p2))))))) ∨ p2) → (p5 → p4))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78032590273019154667227673517 : (((p5 ∨ ((p3 ∨ (p3 ∨ (p5 ∨ (p1 ∨ (p1 ∨ ((p5 → (p5 → ((p3 ∧ True) → False))) → (False → p3))))))) ∨ (p1 ∧ False))) → p1) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ ((p3 ∨ (p3 ∨ (p5 ∨ (p1 ∨ (p1 ∨ ((p5 → (p5 → ((p3 ∧ True) → False))) → (False → p3))))))) ∨ (p1 ∧ False))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706877985689922369328082301539 : ((((((((False ∧ False) ∨ p3) ∧ p5) ∧ p5) ∨ p4) ∨ ((p5 ∧ (False ∧ ((p4 → (p2 ∨ (p4 ∧ (p2 ∨ (p5 ∨ p1))))) → p5))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136723907461340011533747807470 : (((p4 ∧ p3) ∧ (p4 ∨ (((((p1 → ((True ∧ p2) → p2)) → (p2 → p4)) ∨ (p1 ∨ p4)) ∨ True) ∨ (p2 ∨ p5)))) ∨ ((p3 ∧ p1) → p3)) := by
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
theorem thm_5_vars_66307315489138219780137865165 : ((p5 ∨ ((p1 ∨ p1) → ((p5 ∨ p3) ∨ ((p3 ∧ (False ∨ (p5 ∨ (p4 ∧ (p3 → p5))))) → (((p2 ∧ p4) → (False ∨ True)) → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192221231616878985027470518489 : ((((False → ((p1 ∧ (True ∨ p4)) → p3)) → p1) ∧ p3) → (p5 ∨ (((((p5 → p3) → p5) ∧ p3) ∨ (p2 → p1)) ∨ (p2 ∨ (p2 → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168836618953117775423542840225 : ((p3 ∨ ((False ∧ (False → ((p4 ∧ (p1 ∨ (p3 → p4))) → (p4 ∨ True)))) ∨ (p4 → p3))) → ((False ∧ (False ∨ p2)) ∨ (p2 → (False → p2)))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176965423467575291554708775205 : (((p5 ∧ True) → (((((p4 ∧ False) → p5) ∨ p1) ∨ False) → (True ∨ p4))) ∧ (p4 ∨ (p5 ∨ ((((p2 ∨ (False ∧ p1)) ∨ p1) ∨ p5) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h1.left
      let h6 := h1.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180004799090263697971998489234 : ((((p3 → p4) ∧ (((p2 ∧ (True ∧ (p5 ∧ False))) ∨ p2) ∧ p5)) ∨ p1) → ((p1 ∧ ((p1 → ((p3 → p5) → (p5 → p2))) ∧ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739308779726279128804744148052 : ((((p4 ∧ p3) ∨ (((p4 → (p1 ∨ p5)) ∧ False) ∨ (((p2 ∨ p5) ∧ False) → (p4 ∨ (((p1 ∨ (p5 ∧ p4)) ∨ (p2 ∧ p1)) ∨ p1))))) ∨ False) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48145957512964137035744319743 : (((((p1 ∧ False) ∨ False) → (True → (False ∨ (p2 ∨ ((p2 ∨ ((True ∧ (True ∨ False)) ∧ True)) ∧ ((True → p5) → False)))))) → (p3 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80230972915969663055713126061 : ((((((p2 ∧ False) ∨ ((p5 → True) ∧ p1)) → (((p3 → ((False ∧ p3) ∨ (False ∨ p4))) ∨ True) ∧ p1)) ∧ (False → p4)) → (p3 ∧ False)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p2 ∧ False) ∨ ((p5 → True) ∧ p1)) → (((p3 → ((False ∧ p3) ∨ (False ∨ p4))) ∨ True) ∧ p1)) ∧ (False → p4)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h15
    -- Implications on the right can always be decomposed.
    intro h16
    -- False on the left can always be used.
    apply False.elim h16
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h17 := h1 h2
  -- We need to get the right conjuct of h17 based on <expert-advice>.
  let h18 := h17.right
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117277512539642459975689983849 : ((False ∧ (((False ∨ ((((True → ((False ∧ p1) → p4)) ∨ p4) → False) ∨ p2)) ∨ (p2 ∨ (p2 → ((p4 → p3) ∧ p5)))) ∨ p4)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158101337920356868901928103215 : ((((p4 → (True ∧ False)) ∨ p1) ∧ ((p2 ∨ p3) → (((((False ∧ p5) ∧ False) ∨ p5) ∨ p1) ∨ False))) ∨ (p1 → ((False ∧ p5) → (p1 → False)))) := by
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



