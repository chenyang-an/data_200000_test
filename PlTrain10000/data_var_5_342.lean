variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149449916784720095472688080832 : ((False ∧ (((p4 ∨ p4) ∧ (((p3 ∨ ((p2 ∨ p4) ∧ True)) ∧ (p1 ∧ ((p4 ∧ p1) ∧ p1))) ∨ p3)) → p1)) ∨ ((p3 ∧ p1) ∨ (True ∧ True))) := by
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
theorem thm_5_vars_150032431980940104400377078945 : ((p5 ∨ (True ∧ (((((p3 → p3) ∧ (p3 ∧ (p1 → False))) ∧ p1) ∧ (p2 ∧ p2)) ∨ (p1 ∧ (p3 ∧ p1))))) ∨ ((False ∨ True) ∧ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312734221107589780826137806002 : (p3 ∨ (((p2 ∨ (((p2 ∨ p3) ∨ (p5 ∧ (p1 ∨ (p5 → p5)))) ∧ p3)) ∨ (((p5 ∧ (p3 → p4)) ∨ (p1 → (False → p1))) ∨ p1)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50283143348204918272732647554 : ((((((((False ∧ True) ∧ (True ∨ True)) → (p4 ∧ (p3 ∧ False))) ∨ p4) ∨ (True ∧ p2)) → (p4 → p3)) ∨ ((p5 → False) ∨ (p1 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166235342700935693487714338360 : ((p2 ∧ (p2 ∧ ((p2 ∧ ((((False ∨ (p5 ∧ True)) ∧ True) ∧ True) ∨ (p4 ∧ p4))) ∧ p5))) ∨ ((((p1 → p3) ∨ False) ∧ (p4 → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185188924714862811016098200925 : ((True ∧ ((((p4 ∧ p5) ∨ (p2 ∧ (p1 ∧ True))) ∧ p1) ∨ True)) ∨ (p4 ∨ (False ∨ ((p5 ∨ ((p5 ∨ p5) ∧ (p5 → p4))) → (False ∨ p2))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60350477758601775901568616622 : (((p2 → p3) → (p3 → (((p4 ∧ True) ∨ p4) ∨ (((False ∨ (p5 ∨ (p5 ∨ (False ∧ True)))) ∨ p3) ∨ ((p3 ∧ (p1 ∧ p1)) → p2))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624921810748026731387818580084 : ((((p5 ∨ ((p3 ∨ p2) ∧ (p3 ∧ (p2 ∨ (False ∧ ((p2 ∨ ((p1 ∨ (True ∨ p2)) ∧ ((p1 ∧ p5) → (True ∨ True)))) ∧ p2)))))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56934500989577496842650276463 : (((False ∨ (p5 ∧ p2)) ∧ (((False ∧ (((True → False) ∨ (False ∧ ((True ∨ p1) → (p5 ∧ p1)))) ∨ ((True ∧ True) ∨ False))) ∨ p5) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627844588671745076807354435088 : ((((((((True ∧ p5) ∧ ((p5 ∧ ((True ∨ True) ∧ p2)) ∧ True)) → p1) ∧ (p1 ∧ ((False → p1) ∨ (p5 ∨ (p3 → p2))))) ∧ p4) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111594424038919637103592295166 : ((((p1 → ((((p5 ∨ (((True → (False ∨ (p4 ∨ p1))) ∨ (True ∨ p3)) ∨ (p5 → p5))) ∨ p5) → p3) ∧ True)) ∧ True) ∨ True) ∨ (True → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157585716829674900398335488631 : (((p3 ∧ (((p2 → ((p4 → p3) → p4)) ∨ (((p5 ∨ False) → True) ∧ p2)) ∨ p1)) → (p2 ∧ False)) ∨ (True ∧ (True ∨ (False ∧ (p2 ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711050751066140987357047165995 : (((((p3 → p5) → (p4 → (p2 ∧ p5))) ∧ ((p5 → (p3 ∧ (p5 → ((p5 ∧ False) ∧ True)))) → ((p5 → ((p1 → p1) → p3)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146945962510782693693645811558 : (((((False ∧ ((p1 ∧ p3) ∧ (False ∨ (True ∧ (p2 → p3))))) ∨ ((False ∨ p1) → (False ∧ p4))) ∨ p2) ∧ True) ∨ ((p5 ∧ (p5 ∧ True)) → p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179196765377839309682676631088 : ((p3 ∧ (p2 ∧ ((((p2 → p3) ∧ p2) ∧ False) ∨ (p4 ∧ (p1 ∧ False))))) ∨ (p5 ∨ ((p2 ∧ False) → (False ∧ ((p1 → p2) → (False ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223435855725779073177120589833 : ((False ∨ (True ∧ True)) ∧ ((p3 ∨ (p5 ∨ ((False ∧ ((p2 → p1) ∧ p3)) ∨ ((p1 → (p5 ∧ (p1 ∨ False))) → True)))) ∨ (False ∨ (p3 ∧ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303958995986422928003097515623 : (p1 ∨ (((False → (False → (False ∧ p4))) → (((((p2 → p4) → p4) → p2) → False) ∨ (((((p2 ∨ p3) → p3) → p1) ∧ False) → True))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204976035430393691627588657159 : (((p2 ∧ (False → (p3 → p1))) → False) ∨ ((False ∨ (((True ∨ (((p2 ∨ True) ∧ p3) ∧ (p4 → (p3 ∧ p2)))) ∨ (p2 → False)) ∨ p5)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114912857148708912736989593270 : (((((((p4 → ((p5 ∧ p4) ∧ p4)) ∨ False) → p4) → (p5 ∧ p5)) ∨ p1) → (True → ((p3 → (p5 → (p5 ∧ True))) ∧ p2))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670582717311424062120684752897 : (((((p5 ∨ p5) ∨ (p1 ∧ ((((True ∧ True) ∧ ((((p5 ∨ (True → p4)) → p4) ∨ p3) → p4)) → p5) → False))) ∨ (True → (False → p2))) ∨ p3) ∧ True) := by
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
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208359358007009155718606138532 : (((True ∧ p5) ∨ (p4 → (p4 → p1))) → (p3 → (((p1 ∨ (p1 ∨ (((p1 ∨ p4) → p4) ∨ p4))) → p2) ∨ (False → (False ∧ (p1 → p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201330421802067722395053737409 : ((p5 → (((p4 ∧ True) ∧ p2) ∧ (p1 → True))) → (((p4 ∧ False) ∨ (p2 ∨ p2)) ∨ (p1 → (True ∨ (((p3 → (p5 ∧ p4)) ∧ p3) ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46382352171083472789873399282 : ((((p3 ∨ (False ∨ ((True → (p1 ∧ (p1 ∧ p5))) ∧ False))) ∧ (False → (p3 → (True ∧ ((p2 ∧ p5) ∨ (p2 ∨ p2)))))) ∧ (False ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757404754252812429996119098463 : (((p1 ∧ ((False → p4) → (((p3 ∨ (p2 → (((p1 ∧ (False ∨ (p5 ∧ False))) ∨ True) ∧ (False ∨ (p2 ∨ (p1 → p3)))))) ∧ p2) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150002095473946466824153113819 : ((p5 ∨ ((p1 ∧ ((((p4 → p4) ∧ p4) → (p5 ∧ ((p3 ∨ False) ∨ (True ∨ (True ∨ p1))))) ∧ True)) ∧ p4)) ∨ ((p4 ∨ True) ∨ (p5 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639141626786281261324295257910 : ((((((p3 ∨ True) → (p4 ∨ p3)) ∨ (p1 → (p1 ∨ (p2 ∧ ((p1 → ((((p4 ∨ p2) ∧ (False ∨ True)) ∨ True) ∧ p1)) ∧ False))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225571185210527361626442586950 : (((False → False) ∧ p4) ∨ (((p4 → (False ∧ True)) ∧ p2) ∨ ((True ∨ False) ∧ (((p4 → (((False ∧ p3) ∧ (False ∧ p1)) ∨ p4)) ∨ p2) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648484608484073517397991101590 : (((((((((False → p3) ∧ (p3 → (p1 ∨ (False ∧ (((True → True) ∨ p3) ∨ p4))))) ∨ True) ∨ True) ∨ (p3 ∧ p5)) ∨ p5) ∧ (p4 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252755379467620920750437724909 : ((True ∧ True) → ((p2 → (True → ((((((p5 ∨ (p1 → False)) ∨ False) → (((False ∨ p4) ∧ p4) ∨ p5)) → p4) → (p4 ∧ p5)) ∨ p2))) ∨ True)) := by
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
theorem thm_5_vars_177720396924964396043905683396 : ((((p4 ∨ (p1 → (True ∨ (False ∨ p4)))) → (False ∨ (True ∨ p4))) ∧ p5) ∨ ((p4 ∧ ((False ∨ (p2 → (p2 → p1))) ∨ (False ∧ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115416736501463418110640740864 : ((((((p3 → p2) → (p2 → p3)) ∨ p2) ∧ p3) ∨ (((p2 → p3) ∧ (True → ((((p5 → p5) ∧ False) ∨ p5) ∧ p3))) → p3)) ∨ (False ∧ p2)) := by
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
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114710867373979398764357248721 : ((((((p1 ∧ ((p2 → True) → ((p2 ∧ p2) ∨ p5))) → (True → False)) → p4) → p2) → (((p1 → (p5 ∨ p3)) ∧ True) → p1)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190094659649915940627750342483 : (((((False ∧ p3) ∨ (False ∧ p3)) ∨ (True ∨ p1)) ∧ p1) ∨ (p5 → (((p2 → p5) ∨ p4) ∨ (((True ∧ p4) ∧ ((p5 → p4) → p2)) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41891437277147995774455576529 : ((((p1 → (p2 → False)) ∨ ((((p2 → ((p1 → True) → False)) ∧ (p2 → (p3 → ((True ∧ True) ∧ p2)))) ∧ p4) ∨ (True ∧ True))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134025485543099542946382805744 : ((((((p4 ∧ (((((((p3 ∧ True) ∨ p1) ∨ p4) → p4) → p1) ∨ p4) ∨ (False ∧ p1))) ∨ p5) → p5) ∨ p4) ∨ False) ∨ (p4 → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64187452725640712319284301946 : ((False ∨ ((p5 → False) → (((p4 → p1) ∧ ((((p2 ∧ p3) ∨ p4) ∧ (p1 → p3)) → (p4 → (p4 ∧ p1)))) ∨ (True → (True ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740428314123068981160278338755 : ((((p1 ∨ p4) ∨ (((p4 → ((((p4 ∨ True) ∨ ((p5 ∨ (((p5 → p4) ∧ True) ∨ p3)) ∧ (p5 → True))) ∧ p4) → p1)) ∨ False) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241539107672443941993566798477 : ((False → p3) ∧ (((p4 → (p5 → (True ∧ p2))) → ((p2 ∨ p4) ∧ (p3 ∨ p3))) ∨ (p4 → ((p3 → (p4 → (p1 → p5))) → (p3 → p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148166201151813771203859944181 : ((((p1 ∧ ((p5 → (p1 → (((True → p2) → p3) ∧ (p1 ∧ p3)))) ∨ p5)) ∧ p5) ∧ (p4 ∨ (False → p2))) ∨ (False ∨ (True ∨ (p1 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52462245422816163104854063702 : (((False ∨ ((p5 → p4) ∧ ((p1 ∨ ((p3 → (True → p4)) ∨ p3)) → p2))) ∧ (((True ∨ p1) ∧ (((p3 ∧ False) ∧ p4) ∧ False)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714138486930896841668344227941 : (((((p5 ∧ ((p5 → p2) → p5)) → p2) → (False ∧ ((p3 ∨ ((((p5 ∨ ((p5 ∨ p3) ∧ p5)) ∧ p2) ∧ (False → True)) ∨ True)) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247484132641605650197559419526 : ((False ∨ p3) ∨ ((p2 ∨ (p4 ∨ ((((p4 → (True → True)) ∨ (p5 → p3)) ∧ p3) ∨ ((p4 ∧ (p2 ∧ p4)) ∨ p4)))) ∨ ((p3 ∧ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300880752272032149812168847957 : (False ∨ ((((p3 ∨ False) ∧ False) ∨ (((p3 ∧ p4) ∨ (p3 → (p1 ∧ p3))) ∨ True)) ∨ ((((True ∧ p1) → p5) ∧ p2) ∨ ((p2 ∧ True) ∨ p4)))) := by
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
theorem thm_5_vars_775952540602223421083142983753 : (((False ∨ (p2 → (((True ∨ ((((p2 ∨ (p1 → True)) → (p3 → p5)) → p2) ∨ ((p3 ∧ False) → (p2 ∧ p1)))) ∧ (False ∨ p3)) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42951700811255330000614374303 : (((p4 → (False ∨ (p3 ∨ ((((((p4 ∧ p2) → (p2 ∧ p3)) ∧ True) → p2) → ((False ∧ (p1 ∨ p2)) ∨ (p1 ∨ p1))) ∧ p2)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66626784549714123815944858554 : ((True → (((((p1 ∧ True) ∧ True) → ((p4 ∨ p5) ∨ False)) ∧ ((p5 ∨ p5) ∧ p2)) ∧ (((False ∨ p1) ∨ (p5 ∨ p4)) ∨ (p4 ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48561095515672598929531920228 : (((((((p4 → True) ∧ (p1 ∧ False)) ∨ ((p5 ∧ False) ∧ True)) → (((p2 → (True ∧ p4)) ∨ True) ∧ p3)) → p4) ∧ (p2 ∧ (True → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779423708116985904725911129552 : (((p2 ∨ ((((p1 ∧ (p3 ∧ p5)) ∨ ((((False ∧ (p4 ∧ p5)) ∨ p1) ∧ ((p1 → (p4 ∨ (p5 → p2))) ∨ p4)) ∧ p3)) → p5) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112318528768721181459066622517 : (((p3 → ((((((False ∧ (True ∧ p5)) → p3) → (p4 ∨ p2)) ∨ p5) ∧ ((p3 ∧ p1) ∨ (p5 ∨ (p2 → p5)))) → p2)) ∨ True) ∨ (p2 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811545268148263326738909308544 : (((p5 → (True → ((p3 ∧ (p4 ∨ (p1 ∧ (((p2 ∨ ((p2 → False) → (((p3 ∨ (p5 ∧ p4)) ∧ False) → p2))) → p3) ∧ False)))) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305184143369432742466753003084 : (p1 ∨ (((True → p3) ∧ (((p4 ∧ p3) → ((True ∨ (False ∨ False)) ∧ (p2 → False))) ∨ ((p3 → p5) ∨ p3))) ∨ ((p3 ∨ p1) ∨ (False → p5)))) := by
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
theorem thm_5_vars_57376940370071018661466374481 : (((p5 ∧ (p1 ∨ p2)) ∨ ((True → (p3 → ((p5 ∧ (True ∨ ((p3 → True) ∧ p5))) ∨ ((p4 → ((p2 ∧ p4) ∧ p3)) ∧ p4)))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300067672613860909898624136425 : (False ∨ ((((False → p2) ∧ ((p2 → (p4 ∨ p1)) ∧ ((((p4 ∨ True) → False) ∨ True) ∨ (p4 ∧ ((p3 → p3) → p1))))) ∨ True) ∨ (p5 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663194205103491937544039703248 : (((((p3 → p5) ∧ (p3 ∧ ((((p3 ∨ p4) ∧ (p4 ∧ False)) → p3) ∧ (((p5 ∨ p1) → p1) ∨ (p5 ∨ (p4 ∧ p2)))))) → (p4 ∨ p5)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327842770276852333514625369921 : (True → ((((p1 ∨ (p4 → (p1 ∧ (((False ∧ p3) ∧ p2) ∨ True)))) → p4) ∧ (True → (p2 ∨ (((p3 ∧ p2) ∨ p2) ∧ p3)))) ∨ (True ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793512519938053457700589657667 : (((True → (p1 ∨ ((True → (p3 → False)) → ((p3 ∧ (((p5 → p4) ∨ (p2 ∧ ((False → p4) → p3))) ∨ False)) ∧ (True ∨ (p1 → p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136112346842444403483048495760 : ((((p2 ∨ p1) ∨ (((p3 ∨ p3) ∧ p5) ∨ p4)) ∨ ((p2 ∧ (((p2 → p5) ∧ ((p2 → p5) ∨ p1)) ∨ True)) ∧ False)) ∨ ((p2 ∧ False) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67584147645085200798359412645 : ((p1 → ((p4 ∨ False) → (p5 ∧ (((p2 → ((False → (p5 ∧ True)) → p1)) → False) ∨ (((p2 → False) ∨ (p4 ∧ (p3 ∧ False))) ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257612436276053880647466427619 : ((p3 ∨ p2) → ((True ∧ ((True ∧ ((p4 ∧ p2) ∨ ((((p1 → p2) ∧ (False → (p2 ∧ False))) ∨ p4) ∨ (p3 → False)))) ∨ (True → p3))) ∨ p3)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135241667205659744572946184004 : (((((p2 ∨ False) → p4) → (p1 ∨ (True → (p4 ∧ ((p5 ∨ ((p1 → p2) ∨ (True → p1))) ∨ p1))))) → (False ∧ False)) ∨ ((p3 ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350600243227654688693934060684 : (p4 → ((((p3 ∧ p5) → ((p1 ∧ p1) ∨ p4)) → ((p3 → ((True ∧ (False ∨ p5)) ∨ ((False ∨ p4) → (p3 ∨ (False ∧ True))))) ∧ False)) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 ∧ p5) → ((p1 ∧ p1) ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h3
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174181931950557696468904437980 : (((p3 ∨ (((p2 ∨ True) ∧ p4) → (((p3 ∨ p2) ∧ False) ∧ False))) ∨ (p3 ∧ False)) → (((False → (p1 → ((p4 ∨ p1) ∨ p1))) → p2) → p2)) := by
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
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h5 : (False → (p1 → ((p4 ∨ p1) ∨ p1))) := by
        -- Implications on the right can always be decomposed.
        intro h6
        -- Implications on the right can always be decomposed.
        intro h7
        -- False on the left can always be used.
        apply False.elim h6
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h5
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : (False → (p1 → ((p4 ∨ p1) ∨ p1))) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- False on the left can always be used.
        apply False.elim h11
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h10
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133054131202024702778917707118 : ((True → (((((p3 ∧ p1) ∨ (((p1 ∧ (p3 → True)) → False) ∨ (p5 ∨ False))) ∨ (p2 → (p4 ∨ p2))) ∨ p3) ∨ False)) ∧ ((p2 ∧ True) → p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158629076039844862045965652898 : ((p1 ∧ ((((False ∧ p3) ∨ (((((p2 ∧ p1) → False) ∨ True) → False) → (p1 → False))) ∨ False) ∧ p5)) ∨ ((True ∨ p2) ∨ ((p1 ∨ p2) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588218277210292279359639860554 : (((((((((False ∧ p2) ∨ (p5 ∧ p5)) ∨ p2) ∨ p4) ∨ ((((False → False) ∨ (p4 → ((False ∧ p5) ∨ p3))) ∧ p2) ∨ p5)) ∨ True) ∧ True) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260889691903057416504129230326 : ((p4 → False) → (((((p3 ∨ (((p3 ∧ p3) ∧ (p4 ∨ p5)) → (False ∧ (p3 → p5)))) ∧ p5) ∧ ((p4 → p1) → p2)) → (p2 → p2)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175534136724949965990505858282 : ((p4 → (((p5 ∨ False) → True) ∨ (((p3 ∧ (p4 ∨ p4)) ∧ (True → p1)) → False))) → ((p2 ∧ ((False → False) ∧ (p1 ∧ p2))) → (p1 ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122868126142626789354150834499 : (((((p3 ∧ p1) ∨ ((False ∨ p2) → p2)) → (((p5 → p5) → p4) ∧ ((False → (False ∧ True)) ∧ False))) ∧ ((p1 → True) ∨ p4)) → (True → False)) := by
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
    have h6 : ((p3 ∧ p1) ∨ ((False ∨ p2) → p2)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h9
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h6
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h14 : ((p3 ∧ p1) ∨ ((False ∨ p2) → p2)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h17
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h18 := h3 h14
    -- We need to get the right conjuct of h18 based on <expert-advice>.
    let h19 := h18.right
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50482627809589709652915862847 : (((p3 → (((((p5 → p5) → (p5 ∨ p5)) → True) → ((True ∨ p2) ∧ ((p1 ∨ False) ∧ p4))) ∧ p1)) ∨ (((False ∧ False) ∧ p5) → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37269934969610498593458323856 : ((((p5 ∧ (p4 → (((((p3 ∨ p1) ∧ p5) ∨ p5) → ((p5 → (((p1 ∧ True) ∧ (p2 → p4)) ∧ False)) ∧ p3)) → False))) ∧ True) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631052469981985305169243294785 : ((((((((((p4 ∧ (p2 ∨ p1)) → p1) → (p4 → False)) ∨ ((True ∨ (p1 → False)) → p5)) ∨ (p3 ∨ (p1 ∨ p1))) ∨ True) → p5) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215542432669077271469916754767 : ((p4 ∧ (p2 → (p2 → p1))) ∨ (((True ∨ ((p1 ∧ ((p5 ∧ p1) → (((False ∧ p1) ∧ p2) ∨ p1))) → ((True → p5) → True))) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40678822439173276219901436312 : (((((True ∧ (((p5 ∧ (p5 → p2)) ∨ (False ∧ ((p5 → p1) ∧ p5))) → ((p5 → False) ∨ p1))) ∨ ((p5 ∧ True) ∧ p1)) → p5) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46633324556880779421018999460 : (((p4 ∧ (p5 ∨ ((((((p2 ∨ p3) ∧ ((p4 ∨ (p3 ∨ False)) ∨ (False → p5))) ∧ p2) → p3) ∨ p1) ∨ (p5 ∧ False)))) ∧ (p1 ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262203207768934441042399590304 : (True ∧ ((((p1 ∨ True) → ((((p5 → ((True ∨ p4) → p3)) ∧ p2) → (((p4 ∨ (p3 ∧ (p4 ∨ p3))) ∧ p3) ∨ p2)) ∧ False)) → p2) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247592931435760718979086199417 : ((False ∨ p5) ∨ ((p4 ∨ (((((p3 ∧ False) ∨ p2) ∧ True) ∨ (((p4 ∨ p5) → (((p2 ∨ (False ∨ p1)) ∨ p1) → False)) ∨ True)) → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197607970363631305156159956037 : (((p1 → ((p2 ∨ p5) ∧ p2)) ∨ (False ∨ p5)) ∨ (False → (p4 ∨ ((p2 ∧ ((p3 ∨ True) ∨ ((p4 → p2) → ((p2 ∧ p2) → True)))) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693643798195213024293071593957 : ((((((((p1 ∧ p4) ∧ p4) ∧ ((p2 → (p2 ∨ p3)) ∨ p3)) → False) ∨ True) ∨ (((p3 ∧ False) → (p4 ∨ False)) → (False ∨ (p1 ∨ p2)))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_247301402468851383427167541190 : ((False ∨ False) ∨ ((((p4 ∨ True) ∨ (((p2 ∧ (((p4 ∧ p5) ∧ p1) ∧ True)) ∧ ((p4 → p3) ∧ p4)) → True)) → False) ∨ ((p3 ∨ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348786941195371896697181626838 : (p3 → (p1 ∨ (((((((True ∧ True) ∧ p3) → (((p2 → p3) ∨ p3) → p1)) ∨ (((p4 → True) ∨ (p3 ∧ p4)) ∧ p5)) ∧ False) ∨ p1) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_931637646356123078657941730466 : ((((p5 → (False → ((p2 ∨ (p2 → False)) ∨ (False ∨ p5)))) → (True ∧ (((p4 ∧ (p1 ∧ ((p3 → p2) ∧ False))) ∧ True) ∧ (p1 ∧ True)))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → (False → ((p2 ∨ (p2 → False)) ∨ (False ∨ p5)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_26586404791101325256061824450 : (((p2 ∧ True) ∨ ((((p2 ∧ p5) → p5) → (p2 ∧ ((False ∧ True) ∧ p4))) → (((True ∨ (p1 ∧ ((p4 ∧ p3) → p2))) → p2) → p3))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 ∧ p5) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h3
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308525810313068540220393960076 : (p2 ∨ (((((False ∨ p3) → ((p1 → (p1 ∧ False)) ∧ p4)) → ((True ∧ p5) ∨ p1)) ∨ ((p2 → True) ∨ (p4 ∨ ((p5 ∨ True) ∧ p4)))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82214173030437263110911917265 : (((((((p1 ∨ p5) ∨ ((False ∧ p3) → (p4 ∧ True))) → ((p1 ∨ False) ∨ p3)) → (True ∧ False)) ∧ p3) ∧ (p4 ∨ (True ∨ (p3 ∧ p3)))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    have h7 : (((p1 ∨ p5) ∨ ((False ∧ p3) → (p4 ∧ True))) → ((p1 ∨ False) ∨ p3)) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h7
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h17 : (((p1 ∨ p5) ∨ ((False ∧ p3) → (p4 ∧ True))) → ((p1 ∨ False) ∨ p3)) := by
        -- Implications on the right can always be decomposed.
        intro h18
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h5
          case inr h21 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h5
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h23 := h4 h17
      -- We need to get the right conjuct of h23 based on <expert-advice>.
      let h24 := h23.right
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h28 : (((p1 ∨ p5) ∨ ((False ∧ p3) → (p4 ∧ True))) → ((p1 ∨ False) ∨ p3)) := by
        -- Implications on the right can always be decomposed.
        intro h29
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h30
          case inl h31 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h27
          case inr h32 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h27
        case inr h33 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h27
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h34 := h4 h28
      -- We need to get the right conjuct of h34 based on <expert-advice>.
      let h35 := h34.right
      -- False on the left can always be used.
      apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66405161418133112768940261434 : ((p5 ∨ (p1 → (((True ∧ ((p1 ∧ True) → (((p3 ∨ (p2 ∧ (p3 ∨ p1))) → p2) → p5))) ∧ ((p3 ∧ p4) → False)) ∨ (False ∨ p1)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_51222480184595368270901497527 : ((((((False ∧ p3) ∨ p2) ∧ (p4 → p3)) → (((False ∨ False) ∨ ((p4 ∨ p4) → p2)) → p4)) ∨ (True ∨ ((p2 → p2) ∨ (p1 ∨ p3)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112191794208525118194416499516 : (((p5 ∧ (False ∧ (((p3 ∨ (p3 ∧ ((False → (p4 ∨ (((True → p4) → p2) → (p2 ∧ p1)))) ∧ p2))) ∧ p3) ∨ p4))) ∨ True) ∨ (p4 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357100515096897299491241870314 : (p5 → ((p3 ∧ (p1 → p2)) → (p5 ∧ (((p5 ∨ ((p1 → ((p3 ∨ (True ∧ p4)) ∧ (p1 ∨ p4))) → ((p4 → p5) → p5))) → p4) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249130397397280780147765711342 : ((p4 ∨ p2) ∨ ((False ∧ ((p3 ∧ ((False ∧ p4) ∨ p1)) ∧ ((False ∨ True) → p2))) ∨ (p5 → (True ∨ ((((False ∧ p3) ∨ False) → p2) ∧ True))))) := by
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
theorem thm_5_vars_213584248444321052441597132945 : ((((True → p3) ∧ p1) ∨ p2) ∨ (((p3 ∨ (((True → ((p3 ∨ True) ∧ p4)) → (p1 ∨ ((p5 → p1) ∧ (p2 → p4)))) ∧ True)) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59066309164220424548901532568 : (((p5 ∧ True) ∨ ((p3 → ((p4 ∧ False) → p5)) → ((p2 ∨ (False ∨ p1)) → (p3 ∧ (True ∨ (True ∧ ((p4 ∧ (True ∧ p2)) → p3))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46786856240019554843450920444 : (((p4 → (False ∨ (((False → (True ∧ (p5 ∨ False))) ∧ ((p4 → p4) ∧ (p3 ∨ (((p5 ∨ p3) ∨ p2) ∨ p5)))) ∨ p1))) ∧ (p4 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68094970103078304144681502995 : ((p2 → (True → ((((p3 ∨ ((p2 ∧ p5) → ((p5 → ((False ∧ p4) → p3)) ∨ True))) ∧ p1) ∨ p2) → ((p1 ∧ (p5 → False)) ∨ True)))) ∨ p1) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627015635466859636600672343078 : ((((((((p5 ∧ p1) → (((((False ∧ True) → (p3 → (p5 ∨ p5))) → p3) → p5) ∨ p2)) ∨ (False ∨ (p5 → True))) ∧ p4) ∧ p4) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313085190480981167529509601344 : (p3 ∨ (((((p4 ∨ ((p4 ∧ p3) ∨ p4)) ∨ False) ∧ (((((True → p2) ∨ p2) ∧ True) ∨ (p2 → (p1 ∨ p4))) ∨ p5)) ∨ (p1 ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77095392796484114895201287156 : (((((p1 → (False → True)) → p1) ∨ (False → (((p2 ∨ True) ∨ (p4 ∧ (p1 ∧ (False ∨ (p3 → True))))) → ((True ∨ p1) ∧ p4)))) → p3) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 → (False → True)) → p1) ∨ (False → (((p2 ∨ True) ∨ (p4 ∧ (p1 ∧ (False ∨ (p3 → True))))) → ((True ∨ p1) ∧ p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h3
      case inr h7 =>
        -- False on the left can always be used.
        apply False.elim h3
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h3
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- False on the left can always be used.
        apply False.elim h3
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h3
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
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- False on the left can always be used.
        apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h25 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_545254953232397192593477046 : (((((True ∧ (False ∨ (((p2 ∧ p3) → p1) → True))) ∧ False) ∧ ((((p2 ∧ (p5 ∨ p2)) ∧ p5) → (p4 → False)) ∧ p4)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246039445816406861435211662764 : ((p4 ∧ False) ∨ (((p1 → (True ∧ p2)) → p4) → ((p5 ∨ (p1 ∨ (((p4 ∨ p5) ∧ p5) ∨ (p3 ∨ ((p5 ∧ p3) → p3))))) ∧ (True ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40163011372215610338835479486 : ((((((((p1 → p5) ∧ p4) ∧ (p1 → p4)) ∨ p3) ∧ (((p2 → (p2 → True)) ∧ (True ∨ (p5 ∨ (p5 ∧ False)))) ∧ p1)) ∧ p3) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32839797168071288883925332784 : ((p3 ∨ (((((p3 ∨ (p2 → p3)) ∧ (p2 ∨ (True ∧ p5))) → (False ∨ ((((p3 → p3) ∨ (p1 ∨ False)) → False) ∨ p1))) ∨ p1) ∨ True)) ∧ True) := by
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



