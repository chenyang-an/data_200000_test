variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313134747775552916955429014593 : (p3 ∨ (((((p3 → (((True ∧ (p3 → False)) ∨ p1) → (True ∧ p5))) → p4) → (p4 → p3)) ∧ (p1 → (p4 ∧ ((p5 → p3) ∧ True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353956041957436808671113404933 : (p4 → (p3 → (((((True ∨ True) → (p4 → (p3 → (p3 ∧ ((p3 ∧ (((True → p1) ∧ (p1 → True)) ∨ p1)) → False))))) ∧ p2) ∧ True) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191575360939412243032654452655 : ((p2 ∧ ((p3 ∧ ((False ∨ p1) ∧ p1)) ∧ (p2 ∨ p4))) ∨ ((False → True) ∨ ((p1 → p5) ∨ (p4 → (p2 ∧ (((p2 ∧ p2) → False) → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38829200494569097636065895587 : ((((True → (p2 → (p5 ∧ p5))) → ((p2 → ((((p2 → (False ∨ p5)) ∨ p2) ∧ ((True ∧ True) ∧ (True ∨ False))) ∨ p5)) → p2)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191472208021115513521667715982 : ((True ∧ (((p4 → p4) → (p2 ∧ (p1 → False))) ∨ p3)) ∨ ((p5 → (False → p4)) → (((p5 ∨ (p3 → p5)) ∧ p5) → (True → (p1 → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20215397283571642666028938710 : ((((((p3 ∧ (((p2 ∧ p4) ∨ True) ∨ p1)) ∧ p5) → p4) → (p2 → p5)) ∨ ((p5 ∧ True) → ((((p2 → False) ∨ True) → p4) ∨ p5))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749114836783483139196247135451 : ((((p5 → False) → ((p5 ∧ True) → (((True ∧ False) ∨ p4) ∨ ((p4 ∧ p1) ∧ ((p1 → p3) → ((p4 ∧ ((p4 ∨ p5) ∨ p2)) ∧ p3)))))) ∨ p5) ∧ True) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113439249214305998428893675962 : ((((((((False ∧ p1) → (False ∧ p2)) → (False ∧ p2)) ∧ p2) → (p4 → ((p4 → (p1 ∧ False)) ∧ p5))) ∨ True) ∨ (p4 ∨ p5)) ∨ (p3 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148133245253373432113485801038 : ((((p3 ∧ p5) → ((p5 ∧ p1) ∧ (p4 ∨ ((p3 ∧ p2) ∨ (p2 ∨ ((p3 ∨ p5) → p2)))))) → (p4 ∧ p5)) ∨ (True ∨ ((True → p4) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266284579459162586924056278180 : (True ∧ (p5 → (False ∨ (((((p3 ∨ (True → p3)) → (p3 ∧ False)) ∨ True) → (((p5 ∧ p1) ∧ p2) ∨ p2)) → ((p4 ∨ (p5 → p2)) ∨ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195473794030658861550601104693 : (((p2 ∧ (p2 ∨ p2)) ∨ (p3 → (p3 → p3))) ∧ (((True ∨ (False → p5)) ∧ (((p1 ∨ p2) ∨ p3) ∧ True)) ∨ (p4 ∨ ((p5 → True) ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114425126912172510559887229946 : (((p1 ∧ (((p2 → ((((((p3 ∨ p4) ∨ p3) → p2) → p1) ∧ p5) ∨ p1)) ∨ p5) → p2)) ∨ (True ∨ (False ∨ (p3 ∧ p1)))) ∨ (p4 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299250077557567028621432329892 : (False ∨ (((p2 ∨ ((p4 → p5) ∨ ((p4 ∧ ((p5 ∨ ((True ∧ p1) ∨ (p2 ∨ p1))) ∧ p5)) ∧ (p5 ∧ p5)))) → ((p4 ∧ p5) ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115017665579502081472605711476 : (((p2 ∧ (p5 ∨ ((False → p3) → (((False → p2) ∧ p1) → p2)))) ∧ ((p4 ∨ (p3 → (p2 ∧ p3))) → ((p2 ∧ True) ∨ False))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112453304872136073245868519548 : ((((((p2 ∧ ((False ∧ False) ∧ True)) ∨ (p5 ∧ ((True ∧ p4) ∨ (p3 ∧ (p5 ∨ (p2 ∨ p1)))))) → (True ∧ p2)) ∨ p3) → p1) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52675318307344640392461482180 : (((p1 ∨ ((p1 ∨ p3) ∨ (((True → p4) → ((p5 → True) ∧ True)) → p1))) ∨ (True → ((p2 ∧ p5) → ((False → (True ∨ True)) ∨ p5)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57742745072550284372107431404 : ((((p5 ∨ p5) → p2) → ((((((False ∧ p4) ∧ (((p2 → p1) ∧ (((p3 ∨ False) → True) ∧ p1)) → True)) → p3) → False) → True) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300383284568563243557003798360 : (False ∨ ((((((p1 ∧ True) → True) → True) ∨ ((p1 → p2) ∧ p2)) ∧ ((((p3 → p4) → p1) ∨ p1) ∨ (False ∧ False))) ∨ (p5 → (p2 → True)))) := by
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
theorem thm_5_vars_299350976031966753819674306056 : (False ∨ ((((False ∧ True) → p5) → (True ∧ ((p2 ∨ ((False ∨ (True ∧ p3)) ∧ (p2 ∨ p4))) ∨ (p1 → (((p4 → True) ∧ p2) ∨ p1))))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172109172162998093556755465812 : (((p3 → ((p4 ∨ p2) ∧ ((p1 ∨ ((False ∨ p2) ∨ p3)) ∧ p4))) → (p3 ∧ False)) ∨ (((((p4 ∧ p4) → p1) ∨ False) ∧ p2) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261285518009797056777399072829 : ((p5 → True) → ((True → (False ∨ p1)) → (p1 → (((p5 → p3) ∨ (((p3 ∧ ((p5 → p1) → p3)) ∧ (p4 ∨ p2)) ∧ (p3 ∧ p4))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109471040025146587412462594482 : ((p2 ∨ (((p1 → p4) ∧ True) → (((p4 ∧ ((p4 ∨ False) ∨ ((p1 → p3) → False))) ∨ p5) ∨ (p2 → (True → (True ∨ p2)))))) ∧ (p4 → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64644276437786794895295581453 : ((p1 ∨ (p4 ∧ (((p2 ∨ (True ∧ p5)) ∨ p2) ∧ (((p1 ∨ False) → False) → ((p5 → p1) ∨ (((p5 ∨ p5) ∧ p5) → (p3 ∧ p2))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317896421717465288909798305544 : (p4 ∨ ((p1 ∧ (p2 ∨ ((p2 → p1) ∨ (p1 → (p4 ∧ (((False ∨ (p4 → ((False ∧ p4) ∧ (False ∧ p1)))) → (False ∧ True)) → p5)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215535302130840187354912784551 : ((p4 ∧ (p5 ∨ (p5 ∧ False))) ∨ ((((p4 → True) ∧ (p5 → (((False → ((False ∧ p3) ∨ p4)) → True) ∧ True))) ∧ False) ∨ (True ∨ (p4 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219872073725323245837112289233 : ((p3 → (p1 → (False → False))) → (((p2 ∨ ((p5 ∨ ((p5 ∧ p2) ∧ (p1 ∨ False))) ∨ ((p4 ∧ p1) → p1))) ∨ (p3 → (p5 → p4))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592047920348025912461202980685 : (((((p5 ∧ (p4 ∧ ((p5 ∧ (((False ∨ p4) ∨ p4) ∧ ((((p3 ∨ p2) → p5) → False) ∧ p2))) → (p1 ∨ p3)))) ∨ (p5 ∧ p5)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598613295339190379789777927537 : (((((True ∨ (p2 → p4)) → ((((((p2 ∨ p5) ∨ p4) ∧ True) ∧ p3) ∧ ((((p5 ∨ p4) ∨ p3) ∧ True) → True)) → (False ∨ p2))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167915838235598771536210767458 : (((p1 → (p4 ∧ (False ∨ (False ∧ (False ∧ True))))) ∧ (((False ∧ p4) → p4) ∧ (p4 ∧ p3))) → (((p3 ∨ False) → (p2 ∧ p3)) ∨ (p3 ∨ p4))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768227661425496757927385416872 : (((p5 ∧ ((p4 ∨ (p5 → (((p1 ∨ (p3 ∧ p3)) ∨ ((((p3 ∨ p2) ∨ p4) ∨ (p1 → True)) ∧ (p5 ∧ p4))) → p2))) → (p2 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350907442096351440069455270737 : (p4 → ((((False → ((p5 ∧ p4) ∨ (((p2 ∨ p1) ∨ (p1 ∨ p3)) → (p5 ∧ (p5 ∨ False))))) → ((False ∧ False) ∧ True)) ∧ p1) ∨ (True ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245092296409036611942073645251 : ((p1 ∧ p5) ∨ (p5 → (p1 ∨ (((((p1 ∧ (((((p1 → True) ∨ p1) ∨ (True → p1)) ∨ (p1 ∧ p4)) → True)) ∧ p2) ∨ p5) ∨ p3) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56695346291195553481195563159 : ((((False ∧ p4) ∨ p4) ∧ ((((False ∨ (False → p3)) → (p4 ∨ (p5 ∨ ((p5 ∨ p5) ∧ (p3 ∨ (True ∧ p5)))))) ∨ (p2 ∨ p1)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178624944676424238115442279030 : (((((p5 ∧ False) ∨ (p4 ∨ p3)) → p2) → (True ∧ (True ∧ (p4 ∨ False)))) ∨ ((p3 ∧ (p1 → (((p3 ∨ p3) ∧ p3) ∨ p2))) ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309335127873951460980509037326 : (p2 ∨ (((((p4 → ((((True ∨ p3) → p3) → ((p5 ∧ (p3 ∧ (True ∨ p5))) → p4)) ∨ p4)) ∧ p1) ∨ True) → (p5 ∧ False)) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212232165348256984193899451425 : ((False ∨ ((p3 ∧ True) → p3)) ∧ ((((True ∧ p2) ∧ (p4 ∧ (p4 ∧ (p4 ∨ False)))) ∧ p1) ∨ ((False ∧ (p1 → (p1 ∧ (p1 ∨ p4)))) → False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66751856120726836262635848276 : ((True → (p1 ∧ ((False ∨ ((p3 → (False ∧ True)) → ((False ∧ ((False ∨ (False → p1)) ∨ (p5 ∨ False))) ∨ False))) ∧ (p2 ∧ (p4 ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44894891882159932650374398978 : ((((False ∧ (p2 ∨ p2)) → (((False ∧ p3) ∧ (((True ∧ (False → ((p5 ∧ (True → p2)) ∧ (p2 ∨ p1)))) ∨ True) ∧ False)) → p5)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68230216070608059804528233258 : ((p3 → (((((((p2 → (p2 → p4)) ∧ p2) ∧ True) ∨ False) ∨ p1) ∨ (p3 ∨ (((p2 ∨ (p5 → p2)) → p3) ∧ (p2 → True)))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133668195406344259160498573869 : ((((((p3 ∧ ((p3 → (p2 ∧ p1)) → (p2 → (((True ∨ True) ∧ p3) ∨ p2)))) ∧ True) → p4) → (p2 → p5)) ∧ p1) ∨ (p3 → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194600189519388331888537695506 : (((((p5 ∧ True) → (False ∨ True)) ∨ p2) ∨ p4) ∧ ((p3 → (p2 ∨ (p4 → ((((False ∨ False) ∧ (p1 → False)) ∨ (True ∧ p3)) ∨ p2)))) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253844518188859856429184245871 : ((p1 ∧ p3) → ((((p2 → p3) ∧ ((True → True) ∨ (p1 ∧ (((p5 ∨ p4) ∨ p2) ∧ ((True ∨ ((p4 ∨ False) → True)) → True))))) → p4) ∨ p1)) := by
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
theorem thm_5_vars_319612123433144334576853671791 : (p4 ∨ (((p4 ∨ True) ∧ (((False → p1) ∧ p2) ∨ True)) ∧ ((p4 ∨ ((False ∧ False) ∨ p2)) → (((p1 → (p4 ∨ (p5 ∨ p2))) ∨ p5) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248303346280320539697165715150 : ((p2 ∨ p2) ∨ (p3 ∨ (((p3 → p1) ∧ (((((p2 → ((p2 ∨ p5) ∧ p3)) ∧ p3) ∨ p5) ∧ (p5 ∧ (False → p1))) → p3)) → (p1 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_206908065814175796066746909606 : (((((p2 ∧ p1) → p5) ∨ p1) ∧ p4) → ((p3 ∧ (p5 ∧ ((((p3 → p1) ∨ p4) ∨ ((False ∧ (p2 ∨ p3)) → p3)) → False))) → (p2 ∨ p5))) := by
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
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340747446400519899505724328361 : (p2 → ((((((False ∧ p2) ∧ (((False → p5) ∧ p4) ∧ p1)) ∧ False) ∨ (p1 ∨ ((((True ∧ (p5 → True)) ∧ p5) → p3) ∧ p2))) ∨ True) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_876258761233193423002058156820 : ((((((p2 → (((False ∧ (((False ∨ (p1 ∨ (p5 ∨ (False ∧ True)))) → False) ∧ True)) ∧ p4) ∨ True)) ∨ p2) → (p3 → False)) ∧ (True ∧ p3)) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : ((p2 → (((False ∧ (((False ∨ (p1 ∨ (p5 ∨ (False ∧ True)))) → False) ∧ True)) ∧ p4) ∨ True)) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h6
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166518607828823649080408229615 : ((p4 ∨ ((p2 ∧ (p2 ∧ (True ∧ (p2 ∧ (p3 ∧ True))))) → ((p5 → p5) → (p4 ∨ p4)))) ∨ (((p2 → ((p5 ∨ False) ∨ p2)) ∧ True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234497107894614779167788190825 : ((p2 → (True → False)) → (((((False ∨ (p2 ∨ (((True ∨ (p3 → p4)) ∨ p2) ∨ p3))) → p3) ∨ (p1 → (p3 ∧ (p1 ∨ p5)))) ∨ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60802017461633796339872890156 : ((True ∧ (p1 ∧ ((False ∧ False) ∨ ((p1 ∧ ((((True → ((p5 ∧ True) ∨ p2)) ∧ ((True ∨ p3) ∨ (p1 ∧ p5))) ∨ p4) ∧ True)) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53795766025548669759885703371 : (((((((p5 ∨ True) ∧ p5) ∧ True) ∧ (p2 → p3)) → p1) ∨ (((p3 ∧ p2) → (((True ∨ (p1 ∨ p1)) → p3) ∨ (p1 → p2))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340814713732924096519420536424 : (p2 → (((False ∧ (((False → (True ∨ (False ∧ (((p4 → (p3 → p3)) ∨ p2) ∨ p4)))) ∧ (p4 → (p1 ∧ p4))) → p5)) ∧ (p2 ∧ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62073034062337294584446065494 : ((p2 ∧ (False ∧ (p5 ∨ ((True → p3) → (((((False ∧ (p3 ∧ ((p3 ∨ True) → p2))) ∧ p4) ∨ (p1 → p2)) ∧ True) ∧ (p1 ∨ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655432700205304922209472296385 : ((((((True ∨ p5) ∧ ((p2 ∨ (p3 ∧ (((p2 → (p3 → (p1 → p2))) ∨ p4) → True))) ∧ (True ∧ p5))) ∨ (p5 ∧ p3)) ∨ (p2 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48426700564470608401490638722 : (((p3 → ((p5 ∧ (True ∧ p1)) ∨ ((((p4 → p5) → p5) ∨ p3) → (p5 ∨ ((((p1 → True) ∧ p3) ∨ p1) → False))))) → (p5 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63929783720952692936170744597 : ((False ∨ ((((p5 → (p1 ∧ p5)) ∧ (p3 ∨ (((((True ∧ ((p3 ∧ False) ∨ p5)) ∨ p5) → p3) → (p4 → p5)) ∧ p5))) → p3) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250136578297747495267784324881 : ((True → p5) ∨ (((True → (True ∧ p5)) → (((((((p2 ∨ p3) ∨ True) → False) ∧ p1) ∧ p5) ∨ (p2 → (p1 ∨ p5))) ∨ (p5 → False))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225931502260037837460799338716 : (((p2 ∧ p1) ∨ p5) ∨ ((((((p3 → (p2 → p1)) → (((((p5 ∨ False) ∨ p2) ∧ False) → False) ∨ p2)) → False) ∧ p2) ∧ (True ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112829742576878182156059435663 : ((((p4 ∧ (p1 ∧ (p4 → p1))) ∨ (p5 ∨ ((((p2 ∧ p4) → (((p2 ∨ False) → p3) ∨ p5)) ∧ False) → (p3 → p4)))) → p5) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158669660259624036772513792366 : ((p2 ∧ ((((p1 ∨ ((True ∨ True) ∧ p5)) ∧ (((p1 ∧ True) ∨ (False ∨ p3)) ∨ p5)) ∧ p3) ∨ p4)) ∨ (True ∨ (((p3 ∧ p1) ∨ p2) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152844755476126611210443767287 : (((p1 → p5) → (((p4 ∧ p5) ∧ (((p5 ∧ p3) ∨ (True → (p3 → (p2 ∨ p4)))) → (True ∧ True))) ∧ p5)) → (((False ∨ p3) → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42734252346883346731377847796 : (((True → (((p4 → ((p1 → p1) ∧ (((False → p2) ∧ ((p1 ∧ False) → (p1 → False))) ∨ (p5 ∧ p1)))) → p1) ∨ (p1 ∨ p1))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299602046036841153804193690949 : (False ∨ ((((p2 ∧ (p2 ∧ ((p1 ∧ (((((p3 → p1) ∨ p2) → p4) → False) ∧ p4)) → False))) → (p4 → (p4 ∨ (p4 → p2)))) → False) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∧ (p2 ∧ ((p1 ∧ (((((p3 → p1) ∨ p2) → p4) → False) ∧ p4)) → False))) → (p4 → (p4 ∨ (p4 → p2)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262194486248706080758223432835 : (True ∧ ((((((p1 ∨ p4) ∨ ((p2 → (True ∧ p1)) → p5)) → (p1 ∨ p4)) → ((False ∨ p4) ∨ ((False → p1) → (p2 ∨ p5)))) → False) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65581087579065210656304906651 : ((p3 ∨ (p5 → (p3 → (((p1 → ((True → p5) → p2)) ∨ (p4 ∧ ((p5 → p3) → (p5 → (p1 ∧ p5))))) → (True ∧ (p2 ∧ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135399582724759650342321763893 : ((((p2 → ((((False → p5) ∨ (True → p5)) ∧ p1) → False)) ∨ (p3 ∨ (p2 ∧ (False ∨ p3)))) ∨ (p1 ∧ (p4 → p1))) ∨ (p4 ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611916569563231361534111960744 : ((((((((p4 ∧ ((False ∧ (p2 ∧ p2)) → (p3 ∨ p1))) ∧ ((p2 ∧ p3) ∧ (p4 ∧ p1))) ∧ (p1 ∨ p1)) ∧ p5) ∧ (p5 ∧ True)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115125897353668241064816260394 : ((((p2 ∨ (p1 ∧ (p3 ∧ (p5 → p2)))) → ((False → p3) ∧ p4)) → (((p1 ∨ p3) → p2) → (p2 → (p1 → (p3 ∨ p3))))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962409681582983265701068927830 : ((((True → False) ∧ (((p2 ∧ ((p1 ∨ False) ∧ ((False ∨ p5) → True))) → (p2 ∧ True)) ∨ ((p2 ∨ p3) → ((p1 ∧ p1) → (p5 ∨ p2))))) → False) ∧ True) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_514304167415062207321189089290 : ((((p3 ∨ False) ∨ (((p2 ∧ (((p1 ∨ (True → ((p3 ∨ p3) ∧ (p5 ∧ False)))) ∨ p2) ∧ ((p5 ∨ p4) ∧ p1))) ∨ True) ∨ (False → p3))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165322578806058842998513987358 : (((p5 → (True → (((p2 ∧ p5) ∧ (p3 ∧ (p3 ∧ (p5 ∧ p1)))) → p3))) → (p2 → p4)) ∨ ((p4 ∧ (p1 ∨ (True ∨ p4))) → (True ∨ p5))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
theorem thm_5_vars_134173896739628460942233607956 : (((((((p2 ∨ (p2 → ((p4 ∧ (p5 ∨ p1)) ∨ p3))) ∨ p2) ∨ p1) ∨ p3) → (p5 → (p1 ∧ (p4 → False)))) ∨ True) ∨ (True ∨ (p4 ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646778905682340262355018922007 : ((((p2 → ((((p1 → p4) ∧ ((p2 ∧ p2) → p5)) ∨ (((p5 ∨ p5) → ((p3 ∧ False) ∨ p5)) ∨ False)) ∨ (True → (False → p1)))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734142277431689528956856626072 : ((((True ∨ p5) ∧ (((True → (((((p3 ∨ p5) → p3) → False) ∨ p4) ∨ True)) ∧ ((((True → p5) → p2) ∨ p5) ∧ p3)) ∨ (p5 ∨ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160332192472097896509840394870 : (((p2 ∧ ((((p5 → True) → (p5 → p1)) ∧ p3) → (True ∨ ((False ∨ p5) ∨ p4)))) → (False → p5)) → ((((p5 ∧ p5) ∧ p1) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172777422094564095498312346477 : (((p3 ∨ p5) → (p4 ∨ (((p5 ∧ p4) → True) → (p5 ∧ ((False → True) ∧ p2))))) ∨ ((p5 ∨ (True ∨ p5)) ∨ (p2 ∨ (False ∧ (p1 → p4))))) := by
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
theorem thm_5_vars_90451598512616726925271401829 : (((p1 ∧ p1) ∧ (((((((p3 ∧ p3) → (p4 → (((((p2 ∨ True) → False) → p5) ∧ p3) → False))) → False) → p2) ∨ p1) → p4) ∧ p3)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : (((((p3 ∧ p3) → (p4 → (((((p2 ∨ True) → False) → p5) ∧ p3) → False))) → False) → p2) ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196841838651857798198251288593 : (((p5 ∧ ((p2 → False) ∧ (p5 ∨ p5))) ∧ p4) ∨ (((((p5 ∨ p4) → True) ∧ True) ∨ (p4 ∧ False)) ∧ ((p5 ∨ ((p1 ∧ False) → False)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137801868486206397809775523825 : ((p2 ∨ (p5 ∨ (p5 ∧ (((p4 ∧ (p5 ∨ (((p4 ∨ False) ∧ ((True → False) → (p5 ∧ p4))) → p5))) ∨ p3) → p5)))) ∨ (p1 ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724823799464475549159361179482 : ((((p4 ∨ (p1 ∨ False)) ∧ (((((p3 ∧ (p2 ∧ p1)) → p5) ∨ (p4 ∨ p2)) ∨ False) ∧ (((p4 ∧ (p5 → (p5 ∧ p5))) → p5) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54504843939571576235699744856 : ((((False ∧ (p2 ∧ False)) ∨ ((False ∨ p3) ∧ True)) ∨ (((True ∨ ((p1 → p5) ∨ True)) ∧ ((False ∧ False) ∧ (p2 → (p1 → p2)))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131864383941260543875627987470 : (((True ∧ p4) ∨ ((((p4 → ((p5 ∨ p4) → p3)) ∨ True) → ((False ∧ (p1 → p5)) ∨ (False ∨ p4))) ∨ (p3 → p3))) ∧ (True ∨ (p2 ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_837838470835208471403897099019 : ((((((p5 → p2) ∨ ((((p5 ∧ False) ∨ p5) ∧ (p4 ∨ (p1 ∨ ((((False → False) → False) → (p1 ∨ True)) ∨ p5)))) ∨ True)) → p1) ∨ p1) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : ((p5 → p2) ∨ ((((p5 ∧ False) ∨ p5) ∧ (p4 ∨ (p1 ∨ ((((False → False) → False) → (p1 ∨ True)) ∨ p5)))) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808036171137012706752559851148 : (((p4 → (True ∧ (((True ∨ p5) → False) ∨ ((((p5 ∨ (p1 ∨ p2)) ∧ (p5 ∨ False)) ∧ (p1 ∨ False)) ∧ (p5 ∨ ((False ∨ p2) ∧ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310402903289266305478775595414 : (p2 ∨ ((p1 ∧ ((True ∧ p4) ∧ ((p3 ∨ p3) ∧ False))) ∨ ((((True → ((p2 ∨ False) → p4)) → (p4 → p5)) ∨ ((p5 → p1) → True)) ∨ p3))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65952342995281754284782452397 : ((p4 ∨ (p3 ∨ ((p1 → (p3 ∨ ((p5 ∧ (((p4 → p3) ∧ (p4 ∨ ((p2 ∨ True) ∧ p3))) ∧ p2)) ∨ True))) ∨ (p5 ∨ (p4 → False))))) ∨ p5) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330624946006216107528303059123 : (True → (True → (((((p4 ∨ p3) ∧ True) → p5) ∧ (p3 ∨ False)) → (((((p2 ∨ (False → (False → (p4 ∨ p5)))) → p4) → False) ∨ True) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47377991186241322196443446932 : ((((p3 ∧ p3) → (p2 ∧ ((True ∧ (p3 → False)) ∨ ((True ∨ p5) ∧ ((p4 ∨ (False ∧ (p2 → p3))) ∧ (True ∧ p1)))))) ∨ (p2 ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55057644554971226806037909439 : (((p1 ∨ (False → ((True ∧ True) ∧ p1))) ∧ ((p5 → (False ∧ ((((p1 ∨ p4) ∨ True) → (True ∨ (p2 ∧ (p4 ∧ p1)))) ∧ True))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207531546155956048924259019583 : ((((p5 ∧ (p5 ∨ p4)) ∧ p1) → p2) → (False ∨ ((p2 ∧ p1) ∨ (p5 → (p4 → ((((p1 ∨ p1) ∧ p3) ∧ (p3 ∨ p1)) → (p3 ∧ p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  -- Conjunctions on the left can always be decomposed.
  let h15 := h4.left
  let h16 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h15.left
  let h18 := h15.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h20 =>
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h21 =>
      -- One of the premise coincides with the conclusion.
      exact h21
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h23 =>
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h24 =>
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47445686330795666503667926675 : (((p3 ∧ ((p4 → (p5 ∧ p3)) ∧ ((p3 ∧ (p4 ∨ ((((p1 ∨ p2) → ((p4 ∧ False) ∧ p5)) ∨ False) ∧ p3))) → False))) ∨ (p2 → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225436458711728801272342619532 : (((p3 ∨ p4) ∧ p4) ∨ (p2 ∨ ((p1 ∨ ((True ∨ (False → p1)) → ((p3 ∨ (p3 ∧ False)) ∨ True))) ∨ (((True → (p2 → p3)) → p5) → p1)))) := by
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
theorem thm_5_vars_47764044650224666891696934554 : ((((p3 ∧ (p4 → ((p1 → ((p1 → ((p5 → False) ∨ p5)) → ((p3 → (p2 → p5)) ∨ (p1 → p2)))) → p1))) ∨ p1) → (True → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2203021593390465609941425636 : ((p4 ∨ (p3 ∨ (p5 → (p1 ∨ (((p3 ∧ p3) → p1) ∧ (p5 ∧ (False ∧ p3))))))) ∨ ((p2 → True) ∨ (False ∨ (p4 ∧ (False ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684961711332677513912631860077 : ((((p3 ∧ ((p3 → (p4 ∨ (((p5 ∨ (False ∨ p5)) ∧ p5) ∨ ((False ∨ p3) ∨ False)))) ∨ p2)) ∨ (((False ∧ (True → True)) → False) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708098583365644339108183253408 : ((((p5 ∨ (((p1 ∨ True) ∨ p3) ∧ (True ∧ False))) ∨ ((((p2 ∧ p2) → p4) ∧ (p2 ∨ p3)) ∨ (((True ∨ (True ∧ p3)) → p5) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_427705907990814546007614207501 : ((((((((p1 ∧ p3) ∨ p2) → (p2 → (p5 ∧ ((((p1 → False) → False) → True) ∨ ((p5 ∧ False) ∧ p3))))) → False) ∨ p3) ∨ (p2 → True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317634422840261120824412386050 : (p4 ∨ ((((p5 ∨ ((p2 ∨ (p1 → False)) ∨ False)) ∨ (((p1 ∧ (((False ∨ (p3 ∨ p4)) ∨ (p3 ∨ p2)) ∧ p5)) → p2) ∨ True)) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620349317839028582818329366435 : (((((p2 ∨ p2) ∨ ((((False ∨ p1) → ((p5 ∧ p3) ∨ p5)) → True) → ((True ∨ False) → (p2 ∨ (p2 ∨ ((True → False) ∨ p3)))))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590328058792631660339884693172 : (((((((p4 ∨ p2) ∨ p5) ∨ (((False → (((p3 ∨ (p3 ∨ False)) ∧ True) ∨ (True → ((p4 → p3) → p2)))) → p2) ∧ True)) → False) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



