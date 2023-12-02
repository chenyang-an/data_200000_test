variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618684016960108481738387689140 : ((((((p3 ∧ True) ∨ True) ∧ ((p5 ∧ ((p3 ∧ p4) ∨ (((True → (p5 → (False → (p3 ∧ True)))) ∨ p2) ∨ (p3 ∧ p2)))) ∧ p2)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205881868264752487806323296255 : ((True ∧ (((False → p2) ∨ p1) → p3)) ∨ (p1 ∨ ((p2 ∨ p4) ∨ (False ∨ ((((False → True) ∨ p4) ∨ (((p4 → True) ∧ p1) ∧ p1)) ∨ p3))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163245668215899042708228226147 : ((((p5 ∧ (True ∧ (p2 ∨ p1))) ∧ (p2 ∧ True)) → (p4 ∨ (((p1 ∨ p5) ∨ p5) ∨ False))) ∧ ((((p3 ∨ True) → p1) → (p5 → p1)) ∨ p4)) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h14
  -- Implications on the right can always be decomposed.
  intro h15
  -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
  have h16 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h14, we can now drive its conclusion.
  let h17 := h14 h16
  -- One of the premise coincides with the conclusion.
  exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305499488175130418407800335266 : (p1 ∨ (((p4 ∧ (((p5 ∨ (True → p4)) ∧ False) → p1)) ∨ ((False ∨ p3) ∧ p3)) ∨ (p3 → ((False ∧ ((p5 ∧ (p2 ∧ p1)) → p3)) → p2)))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211487637654766941941587159379 : (((p2 ∧ p3) → (p2 ∨ False)) ∧ (p4 → (p1 → (((p1 ∨ False) → ((p1 ∧ (((p3 ∧ False) ∧ (p1 → (p3 ∨ p3))) → False)) → False)) ∨ p4)))) := by
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
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223970203881233590595793188762 : ((p4 ∨ (p3 ∨ True)) ∧ (((p3 ∨ (True → p3)) ∨ False) ∨ (((p5 ∧ p4) ∨ (((p4 ∧ False) ∧ False) ∨ True)) ∨ ((False ∧ (p1 ∨ p3)) ∧ p5)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45392769979980549037360303085 : (((p5 ∧ ((True ∧ (((p1 ∨ p4) ∨ p4) ∧ (((p4 ∨ ((p4 ∨ p4) ∧ False)) ∧ p5) ∨ (((p5 → p2) ∨ p1) → p1)))) → p3)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256052174055558135112286030879 : ((True ∨ p4) → ((((False ∧ (p5 ∨ p5)) ∨ p1) ∨ (True → ((p1 → (p3 ∨ p3)) ∧ p5))) ∨ ((True ∨ ((p2 → p5) → True)) → (False → p3)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46612514736432843834166785009 : (((p3 ∧ (((p1 → (False ∨ (p2 ∨ (((p3 → (p4 → (((p5 → p4) ∨ p4) ∧ p3))) ∧ p3) ∧ p5)))) ∧ False) ∧ p3)) ∧ (p4 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218148006982810857113354766549 : (((p4 → p5) ∧ (True → p5)) → ((p4 ∧ (p5 → ((p5 → (p3 ∧ (p1 ∨ (p2 ∨ (p3 ∧ (p1 ∨ True)))))) ∨ p2))) → ((p3 ∨ p4) ∨ p3))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724964405707869977909814784250 : ((((True → (p4 ∧ p2)) ∧ (((p1 ∧ (p4 ∧ ((p5 ∨ (p4 → (p3 → p5))) → p2))) → ((False ∧ False) ∨ p5)) ∨ (p5 ∧ (True → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231866014545230846806450626579 : (((True ∨ False) → False) → (p2 ∧ ((p5 ∨ ((((p2 ∧ ((p5 → True) ∨ (False ∧ p2))) ∧ ((p4 ∨ (False ∧ False)) ∧ p4)) → False) ∧ p5)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191475158943865410275094962948 : ((True ∧ ((((False → p4) ∧ p3) → (p3 ∧ p3)) → p3)) ∨ ((p3 ∨ (p1 ∧ False)) ∨ (((True ∨ p5) ∨ p4) ∧ (False → (p1 → (p3 ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301300488241992206622548759116 : (False ∨ ((p3 ∧ ((p5 ∨ p3) → (True ∧ False))) → ((p2 ∧ (p2 ∧ ((p4 ∨ p1) ∨ True))) ∨ ((((False ∧ (True ∨ p3)) ∨ True) ∧ p3) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199111122721578792693728514359 : (((((True → p1) → p2) ∨ (p1 ∧ p5)) ∧ p3) → ((p4 ∧ p5) ∨ ((False ∨ (p3 ∨ (True → (((p4 ∨ p4) ∧ (False → p1)) → p1)))) ∨ p2))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618797012797241309180205944944 : (((((p1 ∧ (p3 → p2)) ∧ ((False ∧ (True → p5)) ∧ ((((p1 ∧ (p1 ∨ True)) → p2) ∨ (p4 ∧ p1)) ∨ (p4 → (p1 ∧ True))))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_262229320250763315572575461232 : (True ∧ ((((((p3 → ((p1 ∧ p3) ∨ ((False ∨ False) ∨ (((p5 ∨ p2) → p1) ∨ p4)))) → p5) → p4) ∨ (True ∨ p1)) ∨ (True ∨ p4)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606897687350126936093720998363 : (((((((((True → (False ∨ p3)) ∨ (False → (True ∧ ((p5 → p4) → p5)))) → p1) ∨ p5) ∧ (p4 → ((False ∨ p2) ∧ p3))) ∧ p5) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_57660809163102898416937810243 : ((((p4 ∨ p3) ∨ p1) → (((((p3 ∧ ((True → p5) ∧ p3)) → False) ∧ ((False ∧ p3) ∧ (p1 → p4))) ∧ p1) ∧ (p1 → (p1 ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244761719595181459354275627544 : ((p1 ∧ False) ∨ ((((True ∧ (False ∧ False)) → True) → p5) ∨ (((p1 → ((False → True) ∨ (False ∨ p2))) ∨ p2) ∨ ((p4 ∨ p4) ∧ (p1 → p4))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1459340975222603589480961989 : ((((((p2 ∧ ((((p4 → p5) ∧ p4) ∧ p1) ∧ (p2 → False))) → (True ∧ p2)) → p2) → (p3 ∨ (False ∨ p4))) ∧ p5) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248282914841875689633714270549 : ((p2 ∨ p2) ∨ ((p4 → (((False ∧ (p3 ∧ True)) ∧ p5) ∨ True)) ∨ (((p3 ∨ ((((False → False) ∧ p5) ∨ True) → p2)) ∨ (p5 → False)) ∨ p1))) := by
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
theorem thm_5_vars_765890738245940984363413057786 : (((p4 ∧ ((p1 ∨ (True ∧ (p5 ∨ (True → p2)))) → (False ∧ ((p2 ∨ ((False ∧ (p1 → (p1 ∧ (p5 → p5)))) ∨ p1)) ∨ (p3 ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739244233821514287090635798359 : ((((p4 ∧ p1) ∨ (p1 → (((p5 ∧ p5) ∨ (((True ∧ True) ∨ True) → ((((p5 ∧ (p1 ∧ p4)) ∧ p2) ∨ (p1 ∧ p2)) ∨ p1))) ∨ p1))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53478083840798924108779892131 : (((p1 ∧ ((False → ((p3 ∨ p2) ∧ p3)) ∧ ((p3 ∧ p5) → False))) → (p3 ∧ (((p4 → ((False → (p5 → False)) → p3)) → True) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141624914467201151205657502250 : (((False ∨ (True ∧ p2)) → (p3 ∧ (p4 ∧ (((p4 ∨ True) → (p3 → (False → False))) ∨ (p3 ∨ ((p3 ∧ False) ∧ True)))))) → (p4 → (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602811997680164892472376247682 : ((((p1 ∨ ((((p5 ∨ (((True ∨ p1) ∧ (p5 ∧ ((p1 ∧ p1) → p5))) → (p2 → (True ∧ p2)))) ∧ (False ∧ True)) ∨ p5) ∧ True)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767840005590768601516472239534 : (((p5 ∧ (((p5 ∨ (p3 → ((((False ∧ (True ∨ (p2 ∧ (p4 → p3)))) → (p3 ∧ p2)) ∨ p1) ∨ p3))) → ((p2 ∨ True) → p4)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322639092096222110187212507508 : (p5 ∨ (((((((p1 ∧ (p3 ∨ False)) ∧ (True ∧ ((p2 ∨ p4) ∧ False))) ∨ True) → p3) ∨ (((False ∨ (False ∧ p1)) → True) → False)) ∧ True) → p3)) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (((p1 ∧ (p3 ∨ False)) ∧ (True ∧ ((p2 ∨ p4) ∧ False))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : ((False ∨ (False ∧ p1)) → True) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h8
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113326706288421836785216468877 : ((((p4 ∨ p2) ∧ ((p3 ∨ p1) ∧ (((((((p2 → p1) ∧ p3) ∧ False) ∧ (p2 ∧ p3)) → p2) → p4) → p2))) ∧ (p3 ∨ True)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348831945192001785802315679322 : (p3 → (p1 ∨ (p1 ∨ ((((((p1 ∧ False) ∨ p5) ∧ (((p5 → p3) → p3) ∧ (p4 ∨ True))) ∨ (p1 ∨ (p4 ∨ (p5 → True)))) ∨ True) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_198198282629489832106923408557 : (((p2 → p1) → ((p4 ∨ (p4 → p2)) ∧ p3)) ∨ (((p2 ∧ False) ∧ (((p4 ∨ True) → (((False ∧ p1) ∧ p4) → p5)) ∧ False)) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84055029936525042910262783015 : ((((p3 ∨ (p1 → (p1 → ((False → p5) ∨ ((True → p1) → p5))))) → (p2 ∧ False)) ∧ ((((False → p5) → p1) → p1) → (p1 ∧ p3))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p3 ∨ (p1 → (p1 → ((False → p5) ∨ ((True → p1) → p5))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52986877304308241566621021680 : (((((p5 → p1) → (((p3 ∧ p3) ∧ p3) ∧ p2)) ∧ (p5 → p2)) ∧ (p2 → ((p5 → p3) → (((p5 → p5) → True) → (p2 → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317679520786587004708552948247 : (p4 ∨ ((((p2 ∧ p5) → ((((False ∨ True) ∧ ((((p2 → (p4 → ((p1 → True) → p2))) ∧ p2) ∧ p3) ∨ p4)) ∨ p2) ∨ False)) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649421475667178425107622895246 : ((((((p2 ∧ (((p4 ∧ True) ∨ (p4 → (p1 ∧ p5))) ∧ (((p4 ∨ (p2 ∧ p1)) ∧ p4) ∧ p2))) ∨ p2) ∧ (p2 ∨ p4)) ∧ (p1 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179647214989045902372362839986 : ((p5 → ((((p2 ∨ p2) ∨ ((True ∨ p5) → p4)) ∨ (p1 ∨ False)) ∨ p1)) ∨ (((False ∧ (((p4 → p1) ∧ p3) → p3)) → p5) ∨ (False ∧ p3))) := by
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
theorem thm_5_vars_803315713831897102272938179160 : (((p3 → ((((p1 → (False ∧ (True ∨ p5))) ∨ p2) → (((False ∧ (((p3 → p2) ∧ ((p5 ∨ p4) ∧ p2)) ∧ p1)) ∨ p3) ∨ p4)) ∨ p1)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    exact h1
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774647828886531488836495941764 : (((False ∨ ((((p4 → (True ∧ p4)) ∧ p2) ∨ ((p2 ∨ p1) ∨ p3)) ∨ (((p2 ∨ (p5 ∨ p5)) → (p5 ∧ ((False → False) ∧ p4))) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136362784953354156926209703019 : ((((p3 → (False → p2)) ∧ p1) ∨ (p2 ∨ ((p4 ∨ (((((p5 ∧ (True → p1)) → True) ∧ False) ∨ p5) ∨ False)) ∧ True))) ∨ (p1 → (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156934889854861465958837810977 : ((((False ∨ ((((p4 ∨ p4) ∨ ((p1 ∨ (p5 → p1)) ∧ p5)) ∧ True) ∧ p2)) ∧ (False → p3)) ∨ p4) ∨ (True ∨ ((True ∨ True) → (p3 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609718656714474716219575817759 : (((((p3 ∨ (((((((p5 ∧ True) ∧ (False ∨ p5)) → p3) ∧ p4) ∧ (p3 → ((p1 → p4) ∧ True))) ∧ (p3 → p4)) ∨ p5)) ∨ True) ∨ p2) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129045470308037116640838756768 : ((((False ∧ (p3 ∧ (p5 ∧ (((p2 ∧ (p2 ∧ (p1 ∧ ((p2 ∨ p1) → (p4 ∨ p1))))) ∧ p2) ∧ False)))) ∧ False) ∨ True) ∧ (p3 ∨ (True ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135866940580840872949334308222 : (((((False ∨ ((True → p3) ∧ p2)) → (p5 ∧ p5)) → (p5 ∧ p5)) ∨ ((p5 ∨ p3) → (((False → p3) → False) → False))) ∨ ((p4 ∨ p5) ∨ p2)) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (False → p3) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h4
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (False → p3) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h8
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64265353424145558502249202764 : ((False ∨ (p5 ∨ (p3 ∧ (((((((True ∧ p2) ∨ p2) ∧ (p3 ∧ (False ∨ p5))) → p2) ∧ p3) → p2) ∧ ((p4 → p1) ∧ (p3 → p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_35525054545019420123829984366 : ((p2 → (((False → (p1 ∧ (((p5 ∧ (False ∨ (p5 ∨ p1))) → ((True ∧ False) ∧ p5)) → p1))) ∨ False) → (((False ∨ p4) → False) ∨ p2))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49162729850182769972620479446 : ((((p1 ∧ (p4 ∧ (p2 ∧ (p4 → p5)))) ∧ ((p1 → (p1 ∨ (False ∨ (p4 ∧ p4)))) ∧ (p5 ∧ (False ∨ p3)))) ∨ (True ∨ (p1 ∧ p5))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130898363469724186722370961039 : (((((p1 ∨ p3) ∧ (False ∨ ((p5 → p4) ∧ (p2 ∧ p4)))) ∨ True) ∨ (((False ∨ p2) ∧ (p5 ∧ False)) ∧ (p4 → p1))) ∧ ((p1 → p5) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111902785382105207839427653518 : (((((p2 → (True ∧ False)) ∧ (p5 → (p5 ∧ (False → ((p2 → False) ∨ p1))))) → (True ∧ (True ∧ (p4 ∧ (p3 ∧ p2))))) ∨ True) ∨ (p3 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209015792143585180415650166500 : ((False ∨ ((False → p3) → (p2 ∨ p4))) → (((False → (True ∧ ((p4 → ((False → p1) → p3)) → (p2 → (p2 ∨ p5))))) → (p2 → p3)) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159573299104161115526294335517 : (((p5 ∨ ((p4 ∧ ((False ∨ (p3 → p3)) → p2)) → ((p4 ∧ p3) ∧ ((p3 → p5) ∨ p3)))) ∧ p3) → ((p4 → (False ∨ (p3 ∧ p1))) ∨ p3)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244337340977857719841509183413 : ((False ∧ False) ∨ ((p1 ∧ (p3 → (False ∧ (p1 ∧ p3)))) → (True → ((p5 → (True ∧ (p4 ∨ p3))) ∨ (((False ∧ (p5 → False)) → p3) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113574804363666694906976104772 : (((True ∧ (((True ∨ (p2 ∧ (p4 → False))) ∨ p2) → (p1 ∧ (((p2 ∨ (p3 ∨ p2)) ∨ p2) ∨ (p5 ∧ p2))))) ∨ (False → p4)) ∨ (p3 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661298442072697049757902205699 : ((((((True ∧ (((((p1 ∧ (True ∧ (p5 ∨ (p2 → False)))) → p5) ∨ (False → p2)) → p1) → p2)) ∨ p4) → (p4 → p2)) → (p3 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58536725273239928742627698168 : (((p5 ∨ p3) ∧ ((((((((p4 ∧ False) ∨ (p4 ∨ (True ∨ p5))) ∧ True) → p3) ∧ p1) ∨ p5) ∧ False) ∨ (p4 → ((True ∧ p1) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_823301827165224798820644682124 : (((((p1 → (False ∧ (p1 ∨ (True ∨ p1)))) ∧ ((p5 ∧ ((p2 ∨ True) ∧ ((p4 ∧ ((p5 → p1) ∨ False)) ∨ False))) ∧ (p5 ∨ p5))) ∧ p4) → False) ∧ True) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h17 =>
          -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
          have h18 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h17
          -- We have shown the premise of h16, we can now drive its conclusion.
          let h19 := h16 h18
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h20 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h19
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h21 := h4 h20
          -- We need to get the left conjuct of h21 based on <expert-advice>.
          let h22 := h21.left
          -- False on the left can always be used.
          apply False.elim h22
        case inr h23 =>
          -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
          have h24 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h23
          -- We have shown the premise of h16, we can now drive its conclusion.
          let h25 := h16 h24
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h26 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h25
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h27 := h4 h26
          -- We need to get the left conjuct of h27 based on <expert-advice>.
          let h28 := h27.left
          -- False on the left can always be used.
          apply False.elim h28
      case inr h29 =>
        -- False on the left can always be used.
        apply False.elim h29
    case inr h30 =>
      -- False on the left can always be used.
      apply False.elim h30
  case inr h31 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h32 =>
      -- Conjunctions on the left can always be decomposed.
      let h33 := h32.left
      let h34 := h32.right
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h35 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h36 =>
          -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
          have h37 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h36
          -- We have shown the premise of h35, we can now drive its conclusion.
          let h38 := h35 h37
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h39 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h38
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h40 := h4 h39
          -- We need to get the left conjuct of h40 based on <expert-advice>.
          let h41 := h40.left
          -- False on the left can always be used.
          apply False.elim h41
        case inr h42 =>
          -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
          have h43 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h42
          -- We have shown the premise of h35, we can now drive its conclusion.
          let h44 := h35 h43
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h45 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h44
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h46 := h4 h45
          -- We need to get the left conjuct of h46 based on <expert-advice>.
          let h47 := h46.left
          -- False on the left can always be used.
          apply False.elim h47
      case inr h48 =>
        -- False on the left can always be used.
        apply False.elim h48
    case inr h49 =>
      -- False on the left can always be used.
      apply False.elim h49
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319931783042821232705409614240 : (p4 ∨ ((False ∨ ((p2 ∨ p1) ∧ True)) → (((p3 ∧ (p1 ∧ (((True → (p1 → p4)) ∧ p2) → ((p1 ∧ p5) → p4)))) ∨ True) ∨ (p2 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808697704656021162671171302253 : (((p4 → (p2 → ((False ∧ ((((((p3 → (p1 ∧ p5)) ∨ False) → p2) → True) ∨ p4) → (p2 ∧ p3))) ∨ (((p5 → True) → p1) ∨ p4)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683672585091849838086851447408 : ((((((True → p5) ∨ ((False ∨ (p2 ∨ ((p5 ∧ ((p3 ∨ p1) ∧ True)) → p1))) ∧ p2)) ∧ p4) ∨ ((((True → p1) → p3) ∨ p3) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40949562712043314995497073222 : (((((((p5 → (p5 ∧ (((p4 ∨ p2) → p2) ∨ (p1 ∨ ((p2 ∨ True) → p3))))) → p2) ∨ p1) ∨ (p5 → False)) ∨ (p4 → p2)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7948600134683502622431446903 : ((((((((p1 ∧ (p4 ∨ p1)) ∧ (False → p4)) → (True → p5)) → (False ∧ (((p2 → (p4 ∧ p1)) → True) ∨ p5))) ∧ True) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_665779062294930499152486215974 : (((((((p1 ∨ ((((True ∨ (p1 ∨ False)) ∧ p3) ∧ p3) → (p3 ∧ (False → (p2 ∨ True))))) ∨ p1) ∨ p5) → False) ∧ ((p4 ∨ p5) → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64414562449203765512941511302 : ((p1 ∨ ((p1 ∧ (p1 → ((((p4 → (((True ∨ (p2 ∨ True)) → (p4 ∨ p5)) ∨ (False → p4))) ∧ False) ∧ (True ∧ True)) ∧ p2))) → p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316559884328800969993355320388 : (p3 ∨ (p3 ∨ ((((p2 → (((p5 → (p3 → p4)) ∨ (((True ∨ p3) → p5) ∧ p3)) ∧ (p2 ∨ p2))) → p5) → (p4 ∧ p2)) ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_257972888646151420836948546441 : ((p4 ∨ p1) → ((((p4 → (p4 ∨ ((((p3 → (p5 ∧ False)) ∧ (False → ((p2 ∧ p3) → p1))) ∧ p2) ∨ (p3 → p2)))) → p3) ∧ p3) ∨ True)) := by
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
theorem thm_5_vars_808411943843239875658781619490 : (((p4 → (p2 ∨ ((p1 ∧ (((False ∧ p3) ∨ ((p5 ∨ (True ∧ p4)) ∨ (p5 ∨ (False ∧ (p4 ∧ p5))))) → (p4 ∧ (p2 → p1)))) ∨ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_798791274819763148872724853868 : (((p1 → ((p2 ∧ (True ∨ p4)) ∨ ((p5 → (((((True → p2) ∧ ((p4 → p5) ∧ False)) ∧ (p2 ∨ (p4 → False))) ∨ True) ∧ False)) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679691484283344713937450271137 : ((((((p4 ∨ (p1 ∨ ((p4 ∧ (p3 ∨ (p2 ∧ ((p1 → p5) ∨ p3)))) → (p3 ∧ p3)))) ∨ False) ∨ True) → (p5 ∨ ((p5 → False) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115907589983109015620161527005 : ((((False ∧ p5) ∧ (p5 ∨ p5)) ∨ ((p2 ∧ (((p4 ∧ p3) → p2) ∧ ((((p2 ∧ p5) ∧ p3) ∨ (p3 ∧ p3)) ∨ p3))) ∨ p4)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186910961651390806746984969862 : ((((p4 ∨ p1) ∨ p2) ∧ (((p5 ∨ (p5 ∨ False)) ∧ p1) ∨ True)) → (p2 → ((p3 ∧ p5) ∨ ((False → (p4 → (p2 ∧ (p2 ∨ p5)))) ∨ p1)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h9
          case inr h13 =>
            -- False on the left can always be used.
            apply False.elim h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h15
        -- Implications on the right can always be decomposed.
        intro h16
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h15
        -- False on the left can always be used.
        apply False.elim h15
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h20
          case inr h24 =>
            -- False on the left can always be used.
            apply False.elim h24
      case inr h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
  case inr h26 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h30 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h29
      case inr h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h29
        case inr h33 =>
          -- False on the left can always be used.
          apply False.elim h33
    case inr h34 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h35
      -- Implications on the right can always be decomposed.
      intro h36
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h35
      -- False on the left can always be used.
      apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254638024880351914921582484119 : ((p3 ∧ p2) → ((p3 → ((((p1 → p5) ∧ p3) ∧ ((p2 ∧ (p2 ∧ (False ∨ ((p3 → p1) ∨ (False ∨ (True ∨ p2)))))) ∨ p5)) → p4)) ∨ True)) := by
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
theorem thm_5_vars_157892364197179579413971758797 : (((True → (p2 ∨ (((p4 ∧ (p2 → p5)) ∨ p1) ∨ p1))) ∨ ((p4 ∨ (p4 → (p4 ∨ p5))) ∨ p2)) ∨ ((p5 ∧ (p1 ∨ p4)) ∧ (True ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341987406339326442144207970959 : (p2 → ((((p1 → ((False ∧ p3) ∧ False)) ∧ ((True ∧ (p1 ∧ (p3 → False))) ∧ p3)) ∨ (p1 ∨ (False → (p1 ∨ False)))) ∨ ((p4 ∨ p5) ∨ p4))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113341843279108449184047500513 : (((True ∧ (((((p3 ∨ p2) ∧ p1) ∧ p4) ∨ (((p3 ∧ False) ∧ False) → (True ∨ (True → (p1 ∨ True))))) ∧ p1)) ∧ (False ∨ p2)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340877792748016768614469628187 : (p2 → ((((p3 ∧ True) → (((((p4 → True) → (p2 → p4)) ∨ False) ∧ p4) ∧ (p5 ∨ p1))) ∨ (p2 ∨ (True ∨ (False ∨ (p2 → p4))))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640898923698777860538009985929 : (((((p5 → p3) ∧ (((False → (((p4 → ((False → (p3 ∧ p2)) → ((False → p5) ∧ p5))) ∧ (p4 ∨ p1)) ∨ p5)) → p4) ∨ p5)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3268226801754128352759194735 : ((p1 → p5) ∨ ((p3 ∧ (p4 → ((((p3 ∧ p3) ∧ False) ∨ p3) → (p1 ∧ ((p4 → False) ∧ True))))) ∨ ((p2 ∨ (False ∧ True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233224718618610101642239588979 : ((p5 ∧ (p3 → p5)) → (((p4 ∧ p4) → (p3 ∨ (p2 → (((((True ∨ True) → False) ∧ p2) → (True → (p5 ∨ p5))) → (p1 ∨ False))))) ∨ True)) := by
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
theorem thm_5_vars_194150145566217232532710658053 : ((p1 → (False ∧ (((p1 → p3) ∧ (p5 ∧ p5)) ∨ p4))) → (((((p4 → ((p5 ∧ (p1 → p5)) ∧ p2)) ∧ p3) ∧ (p4 ∧ False)) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172117061810756096251636434888 : (((((((p1 → True) ∧ p3) ∨ p2) ∨ (p3 → p5)) ∨ False) ∧ ((True ∨ True) ∧ p4)) ∨ (((p3 → p5) ∨ ((True → p2) ∨ (False → True))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_218886495976490129819181064309 : ((p2 ∧ (p5 → (False → p4))) → ((((((p1 → (p5 ∨ False)) ∨ ((p1 ∧ (p3 → (False ∨ False))) ∨ (p4 → False))) → p5) ∧ p3) ∨ p2) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246764272269160830584229821040 : ((p5 ∧ p5) ∨ (((p1 ∨ ((p2 ∨ p1) ∨ (p1 → True))) ∧ False) ∨ (True ∧ (((p3 → p3) ∨ ((p5 → (False ∨ (p1 ∧ p2))) ∧ True)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338078430104998805352609944056 : (p1 → ((p3 ∧ (True ∨ (True ∧ ((False ∨ p3) ∨ (True ∨ p5))))) → (((p4 ∨ p5) ∨ ((p5 → (p3 → p5)) ∨ p1)) ∧ ((p5 ∨ p3) ∨ p3)))) := by
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
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h2.left
  let h16 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h23
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352800523007627940572843765375 : (p4 → ((p2 ∨ p5) → (((((p1 ∨ p2) ∨ p5) ∧ p5) → (((p4 → (p4 → ((p1 ∧ False) ∨ p5))) ∧ True) ∧ p4)) ∨ (False → (False ∧ True))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54671818984411928281365263402 : (((((((False ∧ False) ∨ p2) ∧ False) ∨ False) → True) → (((p5 ∧ p4) → p2) ∨ (((True ∨ p1) ∨ ((True → p3) ∨ True)) ∨ (p1 → p1)))) ∨ p3) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781785397964184470783058552980 : (((p2 ∨ (True → ((((p5 ∨ (p2 ∨ p2)) ∧ (((p4 ∧ (p2 ∨ True)) → (p5 → (True ∨ (True ∧ False)))) → (p3 ∨ p1))) ∨ p4) ∨ True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_615366067786963077208922089484 : (((((((p1 → (True ∨ p3)) → p3) → ((p4 ∧ (((p5 → p3) ∨ False) ∧ p1)) ∨ p1)) ∨ ((p2 → (p3 → False)) ∨ (p2 ∧ p3))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690563937394646309268966974926 : (((((((p5 ∨ p2) ∧ (((((p1 → p3) ∨ p3) → False) ∨ p3) ∨ False)) ∧ p2) ∨ p2) → (p4 ∨ (((p5 → p3) → p1) → (p3 → p1)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
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
          -- Implications on the right can always be decomposed.
          intro h11
          -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
          have h12 : ((p1 → p3) ∨ p3) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h11
          -- We have shown the premise of h9, we can now drive its conclusion.
          let h13 := h9 h12
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- Implications on the right can always be decomposed.
          intro h16
          -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
          have h17 : (p5 → p3) := by
            -- Implications on the right can always be decomposed.
            intro h18
            -- One of the premise coincides with the conclusion.
            exact h16
          -- We have shown the premise of h15, we can now drive its conclusion.
          let h19 := h15 h17
          -- One of the premise coincides with the conclusion.
          exact h19
      case inr h20 =>
        -- False on the left can always be used.
        apply False.elim h20
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h24
          -- Implications on the right can always be decomposed.
          intro h25
          -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
          have h26 : ((p1 → p3) ∨ p3) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h25
          -- We have shown the premise of h23, we can now drive its conclusion.
          let h27 := h23 h26
          -- False on the left can always be used.
          apply False.elim h27
        case inr h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h29
          -- Implications on the right can always be decomposed.
          intro h30
          -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
          have h31 : (p5 → p3) := by
            -- Implications on the right can always be decomposed.
            intro h32
            -- One of the premise coincides with the conclusion.
            exact h30
          -- We have shown the premise of h29, we can now drive its conclusion.
          let h33 := h29 h31
          -- One of the premise coincides with the conclusion.
          exact h33
      case inr h34 =>
        -- False on the left can always be used.
        apply False.elim h34
  case inr h35 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h36
    -- Implications on the right can always be decomposed.
    intro h37
    -- We want to use the implication h36 based on <expert-advice>. So we show its premise.
    have h38 : (p5 → p3) := by
      -- Implications on the right can always be decomposed.
      intro h39
      -- One of the premise coincides with the conclusion.
      exact h37
    -- We have shown the premise of h36, we can now drive its conclusion.
    let h40 := h36 h38
    -- One of the premise coincides with the conclusion.
    exact h40
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56544564255251233919188462157 : (((p2 ∨ ((p2 ∨ p5) ∨ p4)) → ((((p1 → (p4 ∧ p1)) ∧ (p5 → (p2 ∨ (False → (p3 ∨ p5))))) → ((True ∧ p3) ∨ p2)) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137491151814020199050514683150 : ((p5 ∧ (((p3 ∧ (p2 → ((p4 → p2) → (p2 ∧ (True → ((p2 ∧ ((p4 ∨ True) ∧ p3)) → p4)))))) ∨ False) → p5)) ∨ ((p1 → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45122666251950840054298817069 : ((((True → p2) → (((((p2 ∨ p4) ∧ (((p5 → p1) ∧ (True → p5)) ∧ True)) ∧ p1) ∧ p5) ∨ ((p2 ∧ (p1 ∧ False)) ∧ p2))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137537979519384574753333081047 : ((p5 ∧ (True → (((p5 → (p2 ∨ ((False → p3) ∨ False))) → p1) ∨ (p3 ∨ ((False → p1) → (p1 → (p1 ∧ False))))))) ∨ (p1 → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116895177711891219924224773720 : (((p4 → p2) ∨ (((True ∧ (p1 ∨ ((((p5 → p1) ∧ (p4 → p2)) → True) ∧ p3))) ∨ (p4 ∨ False)) → ((p1 → p1) → p4))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205093788848974924652121267019 : ((((p2 ∨ p3) ∧ p4) ∧ (p2 ∨ p3)) ∨ ((p2 → (p3 ∧ p3)) ∨ ((p1 → p2) → (p5 → (p4 ∨ (p1 → ((True ∧ (False → p1)) ∨ False))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300055442527666284797177763974 : (False ∨ (((((p4 ∨ ((p2 ∨ p3) ∧ p2)) ∧ p3) → ((((p5 → p1) ∧ p5) ∧ (p2 ∨ (False ∨ True))) ∨ (p1 ∨ p3))) ∧ p4) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654652358667746659924289292952 : ((((((((((False ∧ (p1 ∨ ((p2 ∨ (p3 ∧ p2)) ∧ True))) ∧ (p1 ∧ p4)) ∧ (p4 ∧ False)) ∨ p4) → p2) ∧ p3) → p1) ∨ (True → True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_2821061856934448210019498879 : (((p4 ∨ (p3 ∧ p1)) ∨ p4) → (((p1 → False) ∨ (p4 ∧ (p4 ∨ True))) → (((False → p1) → p3) ∨ (((False → p2) ∧ True) ∨ p1)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h6
        -- False on the left can always be used.
        apply False.elim h6
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h18
          -- False on the left can always be used.
          apply False.elim h18
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h19.left
          let h21 := h19.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h23
        -- False on the left can always be used.
        apply False.elim h23
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h27
          -- False on the left can always be used.
          apply False.elim h27
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h28 =>
          -- Conjunctions on the left can always be decomposed.
          let h29 := h28.left
          let h30 := h28.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h30
      case inr h31 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h32
        -- False on the left can always be used.
        apply False.elim h32
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328568714928586095939283129915 : (True → ((p5 ∨ (p2 → (((False ∨ ((((p1 ∨ False) ∧ p2) ∨ False) ∧ p2)) ∧ p3) → p5))) → (p1 ∨ ((p3 ∨ (p5 ∨ p3)) ∨ (True ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596399318173717762932097602502 : ((((((False → False) → (p5 ∧ (p5 ∧ (p2 ∧ p5)))) ∨ (((p3 ∨ True) ∧ p1) ∨ (False ∨ ((((p2 → False) → True) ∨ False) ∨ p4)))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135780280457050943459071618544 : (((((((True ∧ p2) → (p2 ∨ (p4 → p2))) ∧ p2) ∨ True) ∧ (p5 → p3)) → ((p3 → p1) ∧ (p1 ∧ (p3 ∨ p5)))) ∨ (p1 ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



