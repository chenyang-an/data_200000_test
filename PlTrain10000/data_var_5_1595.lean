variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244128930471835497692878869540 : ((True ∧ p4) ∨ (((p4 → (((p4 → False) ∧ ((False → (p4 ∧ (p4 ∨ p3))) ∧ p2)) → p3)) ∨ ((((p5 → p1) ∨ p4) ∨ p1) ∨ p1)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_932014892527071774513074053260 : ((((((((False → True) ∨ p4) ∧ p2) ∨ True) → False) ∧ (((p3 ∨ (((p3 → False) ∨ False) ∧ False)) ∧ (p1 ∨ p5)) → ((p4 ∨ p5) ∧ p3))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((((False → True) ∨ p4) ∧ p2) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150434960822566120960112378545 : ((((((((((p2 ∧ p4) → p4) ∧ False) ∨ (p2 → (p5 → p2))) ∧ (True ∧ p2)) ∧ p5) ∧ False) → p2) ∧ p1) → (((p5 → False) ∨ True) ∨ p5)) := by
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
theorem thm_5_vars_173418234103581619196998727498 : ((p5 → ((((True → p5) ∨ (False → True)) → p3) ∧ (p2 ∨ ((p4 ∧ p2) ∧ p3)))) ∨ ((False → p1) ∨ (p5 ∨ (True ∧ (True ∧ (p5 ∧ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641490780660690054013059591689 : (((((False ∧ p3) → (((((p1 ∧ ((False ∨ False) → (p4 ∨ p1))) → True) → ((p5 ∨ p4) → True)) ∧ ((False ∨ p1) ∨ False)) → p1)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797343799731932518247469623777 : (((p1 → (((((((((p4 ∨ False) → True) → p5) → p4) ∧ p2) ∨ p4) → p3) → (((p4 → (False ∨ (p3 ∧ p3))) ∧ p2) → p4)) ∨ p1)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_150764014313226786334043882610 : ((((((p1 → True) → ((p1 ∨ ((((True ∧ p1) → (p4 → True)) → p4) → p5)) ∧ True)) ∧ p2) → False) ∨ p1) → ((p1 ∧ (False ∧ False)) ∨ True)) := by
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
theorem thm_5_vars_299462527875146571327213210641 : (False ∨ ((p5 ∨ ((((False ∨ ((False ∨ p5) → p5)) → (((p5 ∧ p3) ∧ p4) ∧ True)) ∨ (p2 ∧ ((False ∨ p1) → (p2 ∧ p5)))) → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147277062302346336157278665456 : ((((((True ∨ p4) ∨ p4) ∧ (p3 ∧ ((False ∧ ((p5 ∨ (True → p5)) ∨ (p5 ∨ True))) ∧ p5))) ∨ p2) ∨ p4) ∨ (p5 → ((p2 ∨ True) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40036296402066779392363452149 : ((((((((True ∧ False) ∧ False) ∨ p4) ∨ ((True ∧ (((p3 ∨ p3) ∨ (p3 ∧ p1)) ∨ p1)) ∧ (False ∧ (True ∨ False)))) ∧ False) ∧ p3) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649443063514943693597927547628 : ((((((p1 ∨ (p1 ∧ ((p3 ∨ (True ∨ ((p4 → (p2 ∨ True)) → (True ∨ True)))) → p3))) ∧ (p3 → p2)) ∧ (p2 ∧ p4)) ∧ (p2 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347616112659132493140148836971 : (p3 → (((p5 → p4) → (False ∧ p1)) ∨ ((p3 → p2) → (((((True ∧ (p3 ∧ p1)) → p5) ∧ p2) → p1) ∨ ((p3 ∨ (p3 ∧ p4)) → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698591965189896043808115129563 : ((((((p1 ∧ p2) ∧ True) ∧ (p2 → ((p3 ∨ p3) → (True ∧ p4)))) ∨ ((True ∨ p3) ∧ ((((p2 ∨ p3) ∨ (True → p2)) → True) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205222215516120528758975700779 : ((((False ∨ p1) ∧ p3) ∨ (p5 ∨ p1)) ∨ (p5 ∨ ((p1 ∧ False) → (p4 → (((p5 ∧ (((p2 ∨ p1) ∧ p5) ∧ (p2 ∨ p3))) ∧ p1) → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55124469994705251562102894259 : (((((True ∨ p3) → (p1 → False)) ∧ True) ∨ (((((p5 → p3) → p1) → p2) → p1) ∨ ((((False ∨ p4) → p2) → (p5 → False)) → True))) ∨ p3) := by
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
theorem thm_5_vars_597682442717640301752997327187 : ((((((False ∨ True) ∨ (p3 ∧ p2)) → ((((p2 ∧ ((p4 → p1) ∨ p5)) ∨ False) ∧ ((p5 ∧ False) ∧ (p5 ∨ (p2 → p4)))) ∧ False)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622328640212786549059112687291 : ((((p3 ∧ ((((p4 → p2) → p4) ∨ ((p3 ∧ (((p1 ∨ p5) → ((p4 → p5) ∧ True)) ∨ p2)) ∨ ((p4 → p4) ∨ True))) → p5)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_598582003875654295552456811893 : (((((p2 ∧ (p3 ∨ p1)) → (((p2 → (False ∨ p1)) ∧ ((p2 ∧ p3) ∧ (p5 ∧ (p1 ∧ False)))) ∨ (p5 ∨ ((p4 ∧ True) ∨ p3)))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37623886261503981998593004747 : ((((((((p1 ∨ (((p4 ∧ p5) ∧ p3) ∧ p4)) → p3) ∧ ((((p3 ∨ (p3 ∨ True)) → False) → p3) ∨ False)) ∧ True) ∨ True) → p4) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190917647490120286110880550927 : (((((p5 ∨ True) → p1) ∧ p3) ∧ (p4 ∨ (p5 ∧ p5))) ∨ ((True → ((((((p3 → p2) → p2) → p3) ∨ p3) ∨ p5) ∨ (True ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50681343499739611728651015126 : ((((p5 ∧ (p2 ∨ (True ∨ p3))) ∨ ((False → ((p1 ∨ p3) ∧ True)) ∨ (p1 ∨ ((p3 ∨ p1) ∨ p3)))) → (p5 → ((p1 ∧ p5) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785755476603906907315533005060 : (((p4 ∨ (((p1 → (p2 ∧ p5)) ∨ ((p4 ∧ (True ∨ p2)) ∨ ((p1 ∨ (p4 ∨ (p3 → (False ∧ p5)))) ∧ (p5 → (p4 ∨ p4))))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755131304401525689298737039026 : (((False ∧ (p2 → (((p5 → True) → ((((p5 ∧ (p5 ∨ ((p3 ∧ p5) → p5))) ∨ (False ∨ p5)) ∨ (False ∨ True)) ∧ p2)) → (p3 ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135733458551726084265571853435 : (((((p2 ∨ ((p5 ∧ False) ∧ p5)) → (((p5 ∧ False) ∨ p2) → p5)) → p5) ∨ ((p3 ∨ False) ∧ (p5 ∧ (False → p3)))) ∨ (p4 → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118152672333030053269265254102 : ((False ∨ ((((p2 ∧ False) → (p5 ∧ p4)) → False) ∨ (((p2 → (p3 → (p1 ∧ ((p3 ∨ p1) → p2)))) ∨ False) ∨ (p5 ∨ True)))) ∨ (p3 → p2)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147471155117617088553226573080 : (((p1 ∧ ((p1 ∧ ((True → ((((((True ∧ p5) ∧ p1) ∧ p2) ∨ p1) ∨ False) ∨ p5)) → p2)) ∨ p3)) ∨ False) ∨ (((False ∧ p1) ∧ p3) → False)) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715831439740291255476524857120 : ((((((p4 → p5) → p4) ∨ p1) ∧ ((((True ∨ ((p3 → p1) ∨ p3)) → True) ∨ (p1 ∨ ((p2 ∧ (p1 ∨ (p1 ∧ p4))) → True))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184499465037539464994610137121 : (((((p5 ∨ True) ∧ p1) → (p3 ∨ (p3 ∨ False))) ∨ (p2 → p1)) ∨ (((p1 → (False → False)) → ((True ∧ (p5 ∧ (p3 ∧ False))) ∨ True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76325032323035109485858332992 : ((((p5 ∧ (True → (((p4 → True) ∨ p5) ∧ (((p2 ∨ False) ∨ False) → (((True ∧ p3) ∨ (p5 ∨ True)) ∧ p3))))) ∨ (p1 → True)) → p1) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ (True → (((p4 → True) ∨ p5) ∧ (((p2 ∨ False) ∨ False) → (((True ∧ p3) ∨ (p5 ∨ True)) ∧ p3))))) ∨ (p1 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165372890419990379400159548901 : ((((((p5 → False) ∧ (p2 ∧ p2)) ∨ ((p3 → p4) ∧ True)) → p3) ∨ ((False ∧ p5) ∧ p3)) ∨ (False → ((True ∨ True) ∧ (p5 ∧ (p2 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224588189283308784358179855275 : ((p2 → (False → p5)) ∧ (p4 ∨ ((p1 ∧ ((((((p3 ∧ p4) ∨ True) → False) ∧ (p4 → ((False ∧ p2) ∨ (p1 ∧ p2)))) ∧ p1) ∧ True)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41840963017369147397097492228 : ((((p2 ∨ (p3 ∧ False)) ∧ (p3 ∨ (p3 ∨ (((True → p1) ∧ ((p4 → p1) ∧ ((p2 ∧ p1) → p4))) → (False → (p1 ∨ p2)))))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762182729811113469913889479554 : (((p3 ∧ (((p5 ∨ p4) ∨ (True ∧ ((((((((p2 ∨ False) → False) ∨ True) ∧ p4) ∨ p5) ∧ True) → (p2 ∧ p4)) → p2))) ∨ (False ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40410045911035321649244312293 : (((((((p2 → False) ∨ (False → ((p1 → True) → p5))) → (p3 ∨ (p3 ∧ (p4 → p3)))) ∧ (p1 ∨ (p4 ∨ (p3 ∧ p5)))) ∨ True) ∨ p5) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48963433745246572802460942410 : (((((p2 → (((False ∨ (p5 → (p3 ∧ True))) → p4) ∧ (((p3 ∨ p5) ∧ (p5 → p4)) ∨ p5))) ∧ True) ∨ p4) ∨ ((p3 ∨ p3) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111390728376791425514511520150 : (((p1 ∨ ((((True ∨ (p5 → True)) ∧ (p4 ∧ True)) ∧ ((p1 ∨ ((p3 → True) ∧ p1)) ∧ (p5 ∨ (p5 ∧ p4)))) ∧ p3)) ∧ p1) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197819513424360329653115820179 : ((((p1 → p1) → False) ∨ (p4 → (False ∧ p1))) ∨ (True ∨ ((p5 → (((((True → p5) ∧ p4) ∨ False) → p3) ∧ (False → p3))) ∧ (p2 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305513394668977291164305573202 : (p1 ∨ ((p5 ∨ ((p3 → (p4 → ((p2 ∧ p5) ∨ (p1 ∨ (False ∧ True))))) → p4)) ∨ (True ∨ (p4 → (p4 ∧ ((True → p1) ∧ (p3 ∨ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325816714655351838156677426020 : (p5 ∨ (p3 ∨ ((((True → p1) ∧ (p4 ∨ p2)) ∨ (p2 ∧ (p5 ∨ (p5 → p1)))) ∨ ((False → ((False → p5) ∨ (True → p1))) ∨ (p5 ∨ p4))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186916299369522682792927396776 : ((((p5 ∧ p2) → True) ∧ (p3 ∨ (p4 → ((p2 ∨ p4) ∧ True)))) → (p2 ∨ ((p3 → ((((False ∨ True) → False) ∨ p3) ∨ p3)) ∨ (p4 ∨ p4)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98987511316124958761089592490 : ((True → ((((((True ∨ ((p2 → (p5 ∧ p2)) → p5)) ∨ False) → False) ∨ False) → p1) ∧ (((p1 → True) → p4) ∧ ((p1 ∨ p2) → p5)))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (p1 → True) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38686009117570308250970311406 : ((((True → (((p2 ∧ p4) → p4) → p2)) ∧ ((p5 ∧ ((p3 ∨ (p5 → p1)) ∨ ((((p3 → p2) → p3) → False) → False))) ∧ False)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142059090562121147814676373313 : ((True ∧ ((p5 → (((p2 ∧ (p3 ∨ (p3 ∧ p2))) ∧ (p4 ∨ ((p2 ∧ (p4 ∨ p3)) → p5))) ∧ (p1 ∨ p1))) → p1)) → ((True → p5) ∨ True)) := by
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
theorem thm_5_vars_320328805330625055052732537714 : (p4 ∨ ((p4 ∨ False) ∨ (p3 → ((((((p5 ∨ (p3 → p4)) ∨ p1) ∨ (True ∨ p3)) ∨ p4) → p5) → (True → (((True ∨ p2) → p5) ∨ p1)))))) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((((p5 ∨ (p3 → p4)) ∨ p1) ∨ (True ∨ p3)) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773308341125590401132708527352 : (((False ∨ (((p5 ∧ p3) ∧ (True → (p4 ∨ (((((((False ∧ (p3 → p1)) ∨ p1) → False) → p3) → True) ∧ (p4 ∧ p4)) → False)))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137632208215164730131851789744 : ((False ∨ (((((p5 ∨ ((False → False) ∨ (True ∧ False))) ∨ (p3 ∨ p4)) ∧ (p4 ∨ (p1 ∨ p3))) ∧ p3) → (p2 ∨ p5))) ∨ (p3 ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257682105130629526247059272110 : ((p3 ∨ p3) → ((((((p5 ∨ p5) ∨ (p1 ∨ (((p5 ∧ p2) ∧ (p5 ∨ p3)) ∨ (p1 → p4)))) → p5) ∧ (p2 ∧ False)) ∨ p1) ∨ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323667937183052822153892664858 : (p5 ∨ ((((p1 → False) → (((False ∧ (p5 → p1)) ∨ False) ∨ True)) ∨ (False → ((False ∧ (True → False)) ∧ p5))) ∨ (True → (p4 ∨ (p3 ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177865661137265082843498650957 : ((((p2 ∧ (((p5 ∧ p4) ∨ (p5 ∨ (False → p2))) ∧ p1)) ∨ True) ∨ p2) ∨ ((((p4 ∧ (False ∨ p4)) → (p5 ∧ p4)) ∧ p3) ∧ (False ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709305359604223679620696289574 : (((((p4 ∧ p3) → ((p3 → (False ∨ p3)) → p4)) → (p3 → (p5 ∨ ((((((p2 ∨ p5) → p1) → p1) → p1) ∨ p4) ∨ (True ∨ p3))))) ∨ p2) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114938258024994936426505190593 : (((((False → (p2 ∨ False)) ∧ p3) ∨ ((False → p1) → (False → (True ∧ True)))) → (p5 ∨ (((p3 ∨ (p2 ∨ False)) ∨ False) ∧ p1))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177895203732079647955371040314 : (((((((p3 ∨ p2) ∧ True) → p5) → (True ∧ False)) ∧ (p3 ∧ p5)) ∨ False) ∨ ((p5 → (p1 ∧ ((False → (True ∧ p4)) ∨ (p4 → p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178880634770238949781014648094 : (((p2 ∧ p5) ∧ ((((p5 → p4) ∨ p1) ∧ (p3 ∨ (False ∧ p5))) ∨ p4)) ∨ (((((p5 ∧ p4) ∧ (p1 ∧ p5)) ∧ (p5 ∨ p1)) → p5) ∨ p3)) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249567060624425367221238074847 : ((p5 ∨ p2) ∨ ((False ∨ p4) ∨ ((((False → False) ∧ ((True → p1) ∨ ((((p5 ∨ False) ∨ False) ∨ p5) ∨ p4))) ∨ p1) ∨ (False → (True ∨ p3))))) := by
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
theorem thm_5_vars_185190993282672434967673479677 : ((True ∧ ((p1 ∧ (p5 ∨ (p3 → ((p5 ∨ False) ∨ True)))) ∨ p3)) ∨ ((p2 → p2) → ((False → (((p1 ∨ p3) → (p2 → p5)) ∨ p1)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204804842536520772846392250603 : (((((p1 → True) ∧ p5) ∨ p4) → p4) ∨ (((True → False) ∧ (p2 ∨ ((False ∧ p4) → ((p4 ∨ p3) → p1)))) ∨ ((True ∨ True) ∨ (p3 ∧ p3)))) := by
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
theorem thm_5_vars_577290355471226493246840157510 : (((p3 → (((p2 ∧ (((True ∧ p2) → (p5 ∧ (((False → p1) ∨ (p1 ∧ p5)) → True))) → p1)) ∧ (p2 ∧ (False → p5))) ∨ (False → True))) ∧ True) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684547163919969883424702115872 : ((((((p5 → p3) ∨ (p2 ∧ p1)) ∧ ((False ∧ p3) ∧ ((p5 ∧ (p4 ∧ p2)) ∨ (False → False)))) ∨ ((p3 ∨ (p2 → (p3 → p3))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59236734549420319833593610245 : (((p2 ∨ p1) ∨ (p5 ∨ (False ∧ ((((p5 ∧ False) ∧ p5) → ((((p3 → p4) ∨ p3) ∧ (True ∧ (p5 → (p3 ∧ p1)))) ∧ p4)) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45768063602309998227325333538 : (((False → (p4 ∧ (((p3 → False) → (p4 ∨ (((((True → ((p2 ∨ p3) ∧ p2)) ∧ (p4 → p1)) ∨ True) → p2) → p5))) ∨ p5))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165164451978155499158743493291 : ((((p1 → p4) ∧ (p5 ∨ ((((True → p5) ∨ (p2 → p4)) ∨ p5) → p1))) ∧ (p5 ∧ False)) ∨ (((p4 ∧ False) → (p5 → (False ∧ True))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47252638938584703913568638898 : (((((p4 ∧ ((True ∨ p5) → p2)) → p3) ∨ (((((p5 ∧ p3) ∧ (True ∨ True)) → (False ∧ (False → p3))) → False) ∨ p5)) ∨ (True ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172899190166736946688610465412 : ((p2 ∧ (((p1 ∨ (p4 ∧ True)) ∨ (False ∧ (p5 ∧ ((p4 ∧ True) ∧ p5)))) ∨ True)) ∨ ((False → (p3 ∨ ((p3 → (p2 ∧ p3)) ∨ p2))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318595089836218737532856721387 : (p4 ∨ (((p3 ∧ ((p3 ∨ p3) ∨ (False ∨ (((False → p2) → (p2 → p4)) → p3)))) ∨ (((p3 → (p5 → p1)) → p5) ∧ p3)) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649528119055006040985961318850 : (((((p3 ∨ ((p1 ∧ ((p1 ∧ ((p1 ∧ (p5 ∨ p3)) ∧ p4)) → ((False ∧ (True ∧ p2)) ∧ p4))) ∨ p2)) ∧ (p1 → True)) ∧ (p2 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159259317645088805590702231903 : ((p3 → (p4 ∨ ((((p4 → (((p5 → ((p5 ∨ False) ∨ p2)) ∧ p2) ∧ p2)) ∧ p1) ∨ False) ∨ p3))) ∨ (((False ∨ (p4 → p4)) ∧ p1) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_918906998038444166110209467946 : ((((((p3 ∨ False) ∨ (True ∨ (True → (((False ∨ p1) → p4) ∨ p2)))) → False) ∧ (((False → (p1 → p4)) ∧ p3) ∨ (p3 ∨ (p1 ∧ False)))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : ((p3 ∨ False) ∨ (True ∨ (True → (((False ∨ p1) → p4) ∨ p2)))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : ((p3 ∨ False) ∨ (True ∨ (True → (((False ∨ p1) → p4) ∨ p2)))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- False on the left can always be used.
      apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14495243557419998515397155334 : ((((False ∧ (((((False → ((p4 → p5) → p2)) ∨ False) ∧ p1) ∧ ((p4 → p3) → p2)) ∨ (False → (p4 ∨ False)))) ∧ p1) ∨ (p2 ∨ True)) ∧ True) := by
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
theorem thm_5_vars_151833600794363592705404524299 : (((p1 → ((True → (False → p1)) → ((p2 → False) ∨ ((p1 ∨ p5) → True)))) ∧ (p1 → ((p1 → p2) → p3))) → (((p3 ∨ p3) ∨ True) ∨ p4)) := by
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
theorem thm_5_vars_191230705857661498940654299909 : (((True → (p2 ∨ p2)) → (((True ∧ p5) ∨ p4) ∧ False)) ∨ ((p4 ∧ ((True ∨ ((p3 ∧ ((p5 ∨ (p4 ∧ p4)) ∨ p3)) ∧ p5)) ∧ p1)) → p1)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113932737821453852521863722597 : (((((False ∨ (p5 ∨ (p2 → p3))) → ((p3 ∨ p5) ∧ p4)) → (((p5 → p1) ∧ p4) ∨ (p5 → True))) ∧ (p3 → (p5 ∨ p5))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38207225329018166937562357367 : (((((p4 → (True ∨ (p2 ∨ ((p4 ∨ (p4 ∧ False)) → ((True ∨ (True → p3)) ∧ p4))))) → (p1 ∨ p3)) → (False ∧ (p5 ∧ False))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183487148228004114393643990000 : ((p3 ∨ ((p4 → p2) ∨ ((False ∧ True) → ((p3 ∧ p4) ∨ p5)))) ∧ (p3 ∨ ((p1 ∨ (False ∨ (p5 → (p1 → p4)))) ∨ ((p4 ∧ False) → p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61112006327824735378893471275 : ((False ∧ ((((((p4 ∨ p1) → p3) ∨ (p1 → (p2 ∨ p4))) ∨ p1) ∨ p5) ∨ ((((p3 → (p3 ∨ p2)) ∧ True) ∨ True) → (p3 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225515791619063711869527359641 : (((p5 ∨ p4) ∧ p5) ∨ (((p3 → True) → p4) ∨ (False → (((p3 → (p2 ∨ False)) ∨ (((p4 ∧ (p5 → p5)) → p2) ∧ (p1 ∧ False))) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_768974821251078850769550397810 : (((p5 ∧ (((True ∨ p5) ∨ False) ∧ (False ∧ (((((p5 ∧ False) ∨ (p1 ∧ p5)) ∧ ((p4 ∧ (p2 ∧ True)) → (False → False))) ∧ True) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66731600384262309374020363156 : ((True → ((True ∨ p4) → ((p3 ∨ p3) → ((p2 ∨ (True → False)) ∨ ((p1 → (False → ((True → p1) ∧ p3))) ∧ (p5 → (p3 ∨ p1))))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    cases h2
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h7
      -- False on the left can always be used.
      apply False.elim h7
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h12
      -- False on the left can always be used.
      apply False.elim h12
      -- Implications on the right can always be decomposed.
      intro h14
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h19
      -- False on the left can always be used.
      apply False.elim h18
      -- False on the left can always be used.
      apply False.elim h18
      -- Implications on the right can always be decomposed.
      intro h20
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h22
      -- Implications on the right can always be decomposed.
      intro h23
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h24
      -- False on the left can always be used.
      apply False.elim h23
      -- False on the left can always be used.
      apply False.elim h23
      -- Implications on the right can always be decomposed.
      intro h25
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45796915852167093494314386092 : (((p1 → ((((p3 → ((p2 ∨ p1) ∧ p4)) ∨ True) → False) ∨ (p5 ∨ (((p3 ∧ (p1 ∧ p3)) ∨ False) → ((True → p4) ∨ p1))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_23723909485085573095969139188 : ((((p3 → (p1 ∧ p1)) → p5) ∨ ((p2 → False) → ((p4 → (p5 ∨ True)) ∧ ((False ∨ p3) → (p5 → (((p2 → p4) ∨ p4) ∧ True)))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h8
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134055103856319375651140767863 : ((((p4 ∨ ((True ∧ False) ∧ ((True ∨ (p1 ∨ False)) → (p3 ∨ ((False ∧ p2) ∨ (True → (p5 ∨ p3))))))) ∨ p3) ∨ True) ∨ (p3 → (p5 → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179205179133410419071388577233 : ((p4 ∧ (((False ∨ (((p3 → False) ∨ p5) → (True → p4))) → p2) ∧ True)) ∨ (((True ∧ (p3 ∧ (p1 → p3))) ∨ True) ∨ ((p3 ∨ p5) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207077994347257668876098247726 : (((p4 ∧ ((p1 → p5) ∨ p5)) ∧ True) → ((p3 ∨ (True ∧ (p3 ∧ (((True → (((p3 → p3) → False) → p4)) → p3) → p4)))) ∨ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
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
theorem thm_5_vars_355536577900741615803590122765 : (p5 → (((p3 → ((((p4 ∨ ((False ∧ (False ∨ True)) ∧ (p1 ∨ False))) → (False → (p5 ∧ p1))) → (p1 → p2)) ∨ p5)) ∧ p4) ∨ (False → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599952640994433554884365928577 : (((((p5 ∧ p1) → ((((False → p5) ∧ (p2 ∨ p1)) ∨ p1) → ((p2 ∨ False) ∨ ((((p5 ∨ (True ∨ p1)) ∨ p4) ∨ True) ∧ True)))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149952288987201083842404864347 : ((p4 ∨ (((((True ∨ ((p1 ∨ p5) ∨ p1)) ∧ (True ∧ p3)) → ((p5 → p2) ∨ (p2 → p4))) ∧ True) ∧ p4)) ∨ (p3 → ((p1 ∨ p1) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137495049910271277947211737399 : ((p5 ∧ ((p4 ∧ (p1 → (p4 → ((False → p5) ∨ ((True → True) ∧ (p3 ∨ ((False → p4) ∧ (p1 ∨ p5)))))))) → p1)) ∨ (p4 ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163279133607218191882985875559 : ((((True → False) ∨ (p4 ∨ (True ∨ p2))) ∧ ((p2 ∧ (True ∨ p4)) → ((p5 ∨ p2) ∨ p3))) ∧ (((p4 → False) → ((p3 ∨ p5) → p4)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125074950579780580158679366632 : (((False ∨ (p4 ∧ p3)) ∧ (p2 ∧ ((p3 ∧ (p2 → p4)) ∧ (p4 ∨ ((p1 ∨ ((False → p3) ∧ (p3 ∧ (True ∨ p2)))) ∨ p2))))) → (p5 ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h21
          case inr h24 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h21
      case inr h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85390422559067821220004850016 : (((((p1 → False) ∨ False) ∧ ((((False ∧ p4) ∨ p5) → False) ∧ p1)) ∧ ((False → p1) ∨ (((p5 → p5) ∨ (p4 ∨ p3)) ∨ (p5 ∨ p5)))) → p5) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h10 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h11 := h6 h10
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h15 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h8
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h16 := h6 h15
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
            have h19 : p1 := by
              -- One of the premise coincides with the conclusion.
              exact h8
            -- We have shown the premise of h6, we can now drive its conclusion.
            let h20 := h6 h19
            -- False on the left can always be used.
            apply False.elim h20
          case inr h21 =>
            -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
            have h22 : p1 := by
              -- One of the premise coincides with the conclusion.
              exact h8
            -- We have shown the premise of h6, we can now drive its conclusion.
            let h23 := h6 h22
            -- False on the left can always be used.
            apply False.elim h23
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- One of the premise coincides with the conclusion.
          exact h25
        case inr h26 =>
          -- One of the premise coincides with the conclusion.
          exact h26
  case inr h27 =>
    -- False on the left can always be used.
    apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356780695487406122650482064363 : (p5 → ((p2 ∨ (((p5 ∨ p3) ∨ p5) → p4)) → (((p4 → (False ∧ ((True ∨ (p2 → p3)) ∨ (((p2 ∧ p5) ∨ p4) ∨ p2)))) ∧ p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_39314571025861325447443501577 : (((p2 ∧ ((((p4 ∧ (((False ∧ (p4 ∨ p2)) ∧ p3) → ((True → p4) → (False ∨ p3)))) → p1) ∨ ((False ∨ p3) ∧ False)) ∧ True)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55446776766799616213706200701 : (((((p4 ∨ False) ∨ (p1 → p4)) → p5) → (((p5 → ((p3 ∧ p5) ∨ (p1 ∨ (p3 → p2)))) ∨ (((p1 ∧ p4) ∧ p5) → p5)) ∧ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254329361866155994124039440910 : ((p2 ∧ p4) → (((p2 ∧ (((p5 ∨ p5) → p5) ∧ (True ∧ ((p3 → p1) ∨ (p5 ∨ ((False ∧ (p1 → p3)) ∧ (p4 ∨ False))))))) ∧ False) ∨ p4)) := by
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
theorem thm_5_vars_135393414902605487576398650742 : ((((p5 ∧ ((((p3 ∨ p2) ∨ p3) ∧ (False → ((True ∧ True) → p5))) → True)) → (p1 ∨ p4)) ∨ (p5 ∨ (p5 → p5))) ∨ ((False ∧ p1) → p2)) := by
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
theorem thm_5_vars_135573370536015013037538886618 : ((((p1 ∧ (((p2 ∧ False) → p2) → (((False ∧ False) ∨ True) → (p3 ∨ p2)))) ∧ p4) ∨ ((True ∨ (True ∨ True)) ∨ True)) ∨ (p2 ∨ (p4 → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260586574617603714325010483045 : ((p3 → p2) → (((p5 → ((((p1 ∨ (p1 ∨ (p2 → p4))) → (p1 → p3)) ∧ p1) ∧ (p2 → p1))) → (p4 → (True ∧ (p3 ∧ p5)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784001635280353310443371902069 : (((p3 ∨ ((True ∨ p1) ∧ (p3 ∨ ((False → ((((p1 → (((p3 ∧ p1) ∨ p1) ∨ p1)) ∨ p2) ∨ (p2 ∧ (False ∧ p4))) ∧ True)) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590206716251999218905136064342 : ((((((True ∨ ((False → (False ∧ p4)) ∧ p2)) ∨ (((p1 ∨ p5) ∨ ((p4 → (p3 ∧ (False ∨ (p1 ∧ p3)))) ∧ p3)) ∨ p1)) → p4) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619489740349142891475881073391 : (((((True → (p3 ∧ False)) → ((p5 ∧ ((True ∨ (((False ∧ p5) ∧ p3) ∨ (p2 → p4))) ∧ (False ∨ (p5 ∨ (True ∨ p2))))) ∧ p2)) ∨ p3) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306567643912426744133597484594 : (p1 ∨ ((p2 ∨ p2) → ((False ∨ ((((((True → p1) → p2) ∧ ((p4 → True) ∧ p2)) ∨ False) ∧ p4) ∨ (p5 ∨ True))) ∨ ((p5 ∧ False) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



