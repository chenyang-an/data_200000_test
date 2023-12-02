variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193506829493466468367593212530 : (((p5 ∨ p4) ∨ ((p3 → True) ∧ ((p5 ∧ p5) ∧ False))) → (((((((p3 ∧ p3) ∧ (p4 → True)) ∧ p5) ∧ (True ∧ True)) → False) ∨ True) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
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
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208482426141749730077987396335 : (((p5 → p4) ∨ ((p4 ∨ p2) ∨ p1)) → ((p1 ∨ (True → (((p5 → p2) ∨ (False ∧ (p1 → p4))) → (p3 → (True ∧ False))))) ∨ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744498632717020495848055743613 : ((((p2 ∧ p2) → ((True → ((p2 ∧ ((((p5 ∧ False) ∨ p3) ∧ ((True → False) → p3)) ∧ p3)) ∨ p4)) ∨ ((p3 ∨ (True ∨ p1)) ∨ True))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50637814771886006908217286585 : (((((p5 ∧ ((True → (p2 ∨ p1)) ∨ p3)) ∧ ((True → p5) ∧ p3)) ∨ (p4 → (p5 ∧ (p5 ∨ False)))) → ((p3 ∨ p2) ∨ (p4 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47744269181561171193953599649 : (((((((p1 ∧ (False → p2)) ∨ True) ∨ p1) ∧ (p2 → (((((True ∧ True) → False) ∨ (p2 ∧ False)) ∧ p4) → p1))) ∨ False) → (p2 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198657541859098531343937109086 : ((p3 ∨ (p4 ∨ (((p1 ∧ p5) ∧ p5) ∧ True))) ∨ (((False ∧ ((p4 ∨ False) ∧ p3)) → (((p3 ∨ (True ∧ p5)) → False) ∨ (False → p4))) ∨ p2)) := by
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
theorem thm_5_vars_716372860773287926567972397960 : (((((p3 ∨ False) ∧ (False ∧ p1)) ∧ (((p2 ∨ True) ∧ p1) ∧ ((p4 → p5) → ((p1 → p5) ∨ (False → ((p4 ∧ (True ∨ p1)) → False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116877982832238970255680779827 : (((p2 → p5) ∨ (((p3 ∧ p3) ∨ (p4 ∨ ((p2 ∧ (p5 ∨ p2)) ∨ True))) ∧ (p1 → (((p1 ∨ (p4 ∨ p3)) ∨ p3) ∨ False)))) ∨ (True ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226784119834105229116634228712 : (((p3 ∧ True) → p2) ∨ ((p4 ∧ (p1 ∧ (((p2 ∨ p1) ∧ p3) ∨ (p1 ∧ False)))) → ((((p1 ∧ p4) ∨ True) → False) ∨ (p4 ∨ (p4 ∨ p4))))) := by
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
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40378221458403247524484066017 : (((((((p5 ∨ p5) ∨ (p2 ∧ (False ∧ False))) ∨ (((p3 ∧ (False → (True ∨ p4))) → (p2 → False)) → p3)) ∧ (p4 ∨ False)) ∨ True) ∨ p2) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191624532037196874330067536501 : ((p3 ∧ (p5 ∨ (((p3 ∨ (p2 ∨ p4)) ∧ p2) ∨ False))) ∨ (p4 → ((((p2 → (p2 ∨ ((p5 ∨ p5) → p2))) ∧ False) ∨ True) ∨ (p4 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114619792945542873763895060651 : (((((p2 ∧ ((((p1 → (p1 ∨ p1)) → p1) ∧ (True → p1)) → False)) ∨ True) ∧ p1) ∨ ((p3 ∨ p5) ∨ ((p4 → p5) → p2))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241517940073250753574025996688 : ((False → p3) ∧ ((((p5 → (p1 ∧ (p5 ∨ p2))) → (p2 ∧ p2)) ∨ ((True ∨ (((((p1 ∨ False) → p5) ∧ True) ∨ p2) ∨ p4)) → False)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125357187848509927799353379377 : (((True → (p3 → p3)) → (((p2 → (((p3 ∨ (((p3 → p2) ∨ p2) ∨ p5)) ∨ (p4 ∧ True)) ∧ (p1 ∨ False))) → p2) ∧ p1)) → (p4 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (True → (p3 → p3)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h3
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172024538964331115037496928839 : ((((p2 → p2) ∧ ((((True ∧ True) ∨ p2) ∧ p3) ∨ (p1 ∨ p5))) ∨ (p2 ∧ p3)) ∨ (False → (p2 ∧ (p3 ∧ (((p2 → False) ∧ False) ∧ p4))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629296421107925537905117228602 : (((((((((True ∨ ((p1 ∧ (p1 ∧ (p2 ∧ p2))) → p5)) ∨ (False → (True → p2))) ∨ (p1 → p5)) → (True ∧ p2)) → p5) ∨ p2) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205505971768713572229319876831 : (((p3 ∧ p5) ∧ (p4 ∧ (p4 ∨ p1))) ∨ (p4 → ((False ∨ ((True ∧ (p3 ∧ p2)) → ((p3 ∨ (((p5 → p3) ∨ p4) ∧ p2)) ∧ True))) ∨ False))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190164595676716848110356305638 : (((p1 ∧ (((p4 → p1) → (p5 ∧ p3)) ∧ p1)) ∧ p1) ∨ (p2 → (p1 → ((False ∧ True) → (((p4 → (True → False)) → p2) ∨ (p1 → p2)))))) := by
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264057495230940378753364944364 : (True ∧ ((((((False ∨ p2) ∨ (p1 → False)) → False) ∨ p2) ∧ p1) ∨ (p1 ∨ (False → ((p5 ∨ (((p3 ∧ p1) ∨ p2) ∨ False)) ∨ (p1 ∨ p5)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219947286578525416238389478914 : ((p5 → ((p3 ∧ p2) ∧ p1)) → (((p2 ∧ (p2 ∨ (((p1 ∧ p4) ∨ p5) → (((p3 ∨ p2) ∧ p3) → False)))) → (False ∧ p5)) → (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135587508457670388823383307520 : (((((((p3 → (p1 ∧ False)) ∧ (False ∧ True)) ∧ p3) ∨ (p2 ∧ p4)) ∨ (p2 ∨ True)) ∨ (((False ∨ p4) ∨ p2) → p2)) ∨ (p5 ∨ (p3 → p3))) := by
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
theorem thm_5_vars_68172219035351326481689111445 : ((p3 → (((((p2 → p1) ∨ (((p2 ∨ (p5 ∨ p4)) ∧ p4) ∨ (p3 ∧ ((p5 ∧ (p5 → p3)) → (p5 ∨ p4))))) → p2) ∧ False) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156785187049476472292194712749 : (((p1 ∧ ((True ∧ (p1 ∧ (p2 ∧ (((p2 ∨ True) ∨ ((p5 ∧ p4) → p5)) → p1)))) ∨ True)) ∧ p5) ∨ ((p5 → p4) → (False → (p5 ∧ p5)))) := by
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
theorem thm_5_vars_148197723890558648104858684709 : ((((p4 ∧ False) ∨ (p4 ∧ ((((True → False) → p4) ∧ ((p3 → p1) ∧ p4)) ∨ p5))) ∧ (p3 ∨ (p1 ∧ p3))) ∨ (p1 ∨ ((p3 → False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668724776656010992710632928739 : (((((((p1 ∨ ((True ∨ p3) ∨ p1)) ∧ (((p5 ∧ (p2 → (p3 ∨ p4))) ∨ p5) → (p4 ∨ False))) ∨ p4) ∨ True) ∨ ((False ∧ p3) → p1)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_694882551038362968030271198320 : ((((p3 → (p4 ∧ (p1 ∧ ((p1 → (p5 ∧ ((p5 ∨ p1) → p5))) ∨ False)))) ∨ (((p5 → ((True → p2) ∨ True)) → (p5 → p5)) ∨ p4)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_260588072727279619324085214291 : ((p3 → p2) → (((True ∨ p4) → ((p4 ∧ (p5 ∧ ((((p4 → p2) ∧ (True ∧ (p4 ∨ p2))) ∧ p2) ∧ p4))) ∨ ((p3 ∧ False) → True))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157585551653223434825977339476 : (((p2 ∧ (p5 → ((p5 → p1) ∨ (((p5 ∧ p2) → (False ∧ (False ∨ p3))) → p2)))) → (p5 ∨ p4)) ∨ (((p3 ∨ True) ∨ p4) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51909648735929050573781931349 : (((((p5 ∧ ((p1 ∧ ((p4 → p1) ∧ (p2 → p1))) ∨ p4)) ∨ p1) ∨ (p3 ∨ True)) ∨ (((True ∨ p2) → ((True → p4) ∧ p4)) → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64132820438936316691839904517 : ((False ∨ (((p3 → (p5 ∧ p5)) ∨ p5) → ((((p4 ∨ ((True ∧ p5) ∧ p1)) → ((p2 ∧ p5) ∧ p5)) ∨ ((p1 ∨ p5) ∨ True)) ∨ p3))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_615293298577402653530988270241 : (((((((((p3 ∧ p4) ∧ (p4 ∨ p1)) → p2) ∧ (p5 ∨ ((p3 ∨ p3) → p4))) ∨ p1) ∨ (p3 ∧ (False → ((False → p5) ∧ p5)))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178199352341283238920869244330 : (((True ∨ (False ∨ (p2 ∧ ((p5 → (False ∨ (p5 ∨ p4))) ∧ True)))) → p5) ∨ ((p3 ∨ (p2 → (True ∧ p3))) → ((p4 ∨ (False → p1)) ∨ True))) := by
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
theorem thm_5_vars_213806854924429699518593711603 : (((p3 ∧ (False ∧ p2)) ∨ p2) ∨ ((False ∨ p5) ∨ ((((p3 ∨ ((True ∧ ((p3 → p4) ∨ ((p4 ∨ True) ∨ p4))) → p2)) ∧ p4) → p4) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47008106803003685522528060515 : (((((True ∨ p3) → (((p3 ∧ (p1 ∧ ((True ∨ (p2 ∨ p1)) ∨ p1))) ∧ False) ∨ (p2 ∨ ((True ∨ False) → p1)))) → p3) ∨ (p1 → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789312765741695123503997818459 : (((p5 ∨ ((p4 ∨ ((((p3 ∧ p2) → p2) ∧ p2) ∨ ((p1 ∨ ((True ∨ True) ∨ p1)) ∨ False))) ∧ (((p5 ∧ (True ∧ p4)) ∨ p5) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615516466632145520862267442504 : ((((((((p2 → p2) → ((p3 ∨ (p5 → p3)) ∨ p2)) → False) ∨ (p1 ∧ (p4 ∧ True))) → ((p1 ∨ ((p3 ∨ p3) ∧ p4)) ∧ p5)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67896244615285226144349203083 : ((p2 → ((False ∧ ((p1 ∧ p5) → ((p4 → ((p1 ∧ (True → True)) ∧ p4)) → (p2 ∧ p3)))) ∨ (p3 ∨ ((p3 → False) ∨ (p2 ∨ False))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37119912715573773575104977096 : (((((p3 ∨ (p3 ∨ (p2 ∧ ((p4 ∧ p3) ∧ ((p3 ∨ (p5 → p4)) ∨ ((True ∧ (p4 → (p4 → p2))) ∨ False)))))) → False) ∧ p5) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216974030414850923712676405764 : (((p3 → (p1 ∨ False)) ∧ p3) → (((False ∨ False) ∧ p2) ∨ (p1 ∨ ((p2 → ((False ∧ False) ∨ (((False → True) → p2) ∨ p5))) ∧ (True ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354694859813094351767204831737 : (p5 → (((False ∧ (((p4 → (((p1 ∨ p2) ∨ ((False ∨ (((p3 → True) → p4) ∧ p5)) → p5)) → False)) ∨ p1) ∨ False)) ∨ (p4 ∧ False)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48994513274206356785840510207 : ((((p5 ∧ ((False → ((p5 ∨ False) → p1)) ∧ (((((p4 → p4) ∧ (False ∧ True)) ∧ p5) ∨ p5) ∨ True))) ∨ False) ∨ (p1 ∨ (True ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686677246419502689812103920452 : (((((p1 → p5) → (((p3 ∨ p4) → (p2 → p4)) → (p1 ∧ (((p5 ∨ p1) ∧ p2) ∧ True)))) → (((p4 ∨ (p1 ∧ True)) → False) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39382175822704822471594668557 : (((p3 ∧ (p1 ∧ (((p2 ∨ p2) ∧ (p1 → (p2 ∨ ((p5 → False) ∨ False)))) → ((((p5 → (False → p1)) → p3) → p1) ∧ p4)))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174532667915782040440928600775 : ((((True ∨ (p1 ∨ p4)) ∨ (p5 ∧ False)) → ((True ∧ p2) ∧ ((p4 ∨ False) ∧ True))) → ((((False → p5) → (True → p2)) ∨ p2) ∨ (p2 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∨ (p1 ∨ p4)) ∨ (p5 ∧ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738990183658548898120012628086 : ((((p3 ∧ p2) ∨ (((((p2 → (p4 ∧ (p3 ∧ (p5 → False)))) ∧ False) → p2) ∨ p5) → (True → ((True → (p2 ∧ (False ∨ False))) ∨ True)))) ∨ p5) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618014593628695604093470166428 : ((((((p1 ∧ (True ∨ p2)) ∨ True) ∧ (((p4 ∨ (p1 ∧ p4)) → (p1 → (((False ∧ p2) ∨ (p3 ∧ (p4 → p4))) → True))) → p5)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149882215626555448347501069644 : ((p2 ∨ ((p2 → (p1 ∨ (((p2 → p4) ∧ p3) ∧ p5))) ∨ ((p4 → True) → ((True → p1) ∧ (p4 → p5))))) ∨ ((p2 → p1) → (p2 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356055782288961927558761467308 : (p5 → ((((True ∨ (p5 ∧ ((p4 → p5) ∨ (((p5 ∧ False) ∧ p2) → True)))) ∨ ((False ∨ p1) ∨ p2)) ∧ p2) → ((p3 ∨ p3) → (False ∨ p5)))) := by
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
    let h5 := h2.left
    let h6 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h2.left
    let h21 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- False on the left can always be used.
          apply False.elim h31
        case inr h32 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
      case inr h33 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343455624846299199511969900208 : (p2 → ((True → p1) ∨ ((p3 ∧ ((False ∧ (((p1 ∨ p3) → (p3 ∧ p2)) ∨ True)) ∨ (p5 ∧ ((p5 ∧ p5) ∧ p5)))) ∨ ((p2 ∧ False) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166008077894369834715216675852 : (((False ∨ p4) ∨ (p2 ∧ (p1 ∨ (p5 ∧ (((((p1 → p5) → True) ∨ True) ∨ p1) → p3))))) ∨ (p1 ∨ ((((False ∨ p3) → True) → p3) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ p3) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341043417855164603610079317064 : (p2 → ((False ∨ ((p3 ∨ ((p5 ∨ ((p4 ∨ False) → (False ∨ True))) → True)) → (((False → p4) → (p1 ∨ p5)) ∨ ((False ∨ p1) → True)))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116867101852010417593411483541 : (((p1 → p5) ∨ (((p5 ∧ (p5 ∧ p4)) ∧ p1) ∨ ((p3 ∧ (p5 → (p5 → (((p1 → p4) ∨ True) ∧ p5)))) ∧ (p1 ∨ False)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656248845995305388105425731257 : ((((((((p4 ∨ p5) → (p2 → (True ∨ True))) → (p4 ∨ p5)) ∧ p4) ∧ (((True → (p1 → (True ∧ p2))) ∨ False) → True)) ∨ (p1 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228180357020656549633679647340 : ((p5 ∧ (p2 ∧ p4)) ∨ (((p5 → p3) ∨ True) → ((((p1 ∧ p4) → ((p2 ∧ True) ∧ p1)) → (((p2 ∧ p1) → p4) → False)) ∨ (True ∨ p2)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259330699516573744685954872731 : ((False → p2) → (((True → p1) ∧ (((p4 → ((p4 ∧ (p1 ∧ p4)) → True)) ∨ (p4 → p5)) → p5)) → (((p2 ∨ p1) → p5) ∨ (p2 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : ((p4 → ((p4 ∧ (p1 ∧ p4)) → True)) ∨ (p4 → p5)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h7
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h12 : ((p4 → ((p4 ∧ (p1 ∧ p4)) → True)) ∨ (p4 → p5)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h15 := h4 h12
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117477682628024838401827814290 : ((p1 ∧ (False ∨ (((((((p4 ∨ (p2 ∨ p1)) ∨ (p1 ∨ p3)) → p1) → p2) ∨ False) ∧ (p4 → p3)) ∧ (True ∧ (False ∧ False))))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119140878890912678619862933379 : ((p1 → (True → (True ∧ ((((p2 ∧ p5) ∨ ((False ∧ (p4 ∨ p4)) ∨ (p5 ∧ (p3 ∨ (p1 ∧ (p1 ∨ False)))))) ∨ p3) ∨ p1)))) ∨ (p3 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167493644212758731991930264808 : (((((False ∧ (p4 ∧ (p2 ∨ True))) ∨ (((p5 ∧ False) → p4) ∧ False)) → p4) ∧ (p4 → p4)) → (((p5 → ((p3 → p4) ∨ False)) ∧ True) ∨ True)) := by
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
theorem thm_5_vars_50595243524576820500446779044 : (((((p1 → p3) ∨ (p3 ∧ ((p5 → ((((p1 → True) ∧ False) → p2) ∧ p5)) → p1))) ∧ (p5 → p1)) → ((p4 ∧ (p5 ∨ p4)) ∨ True)) ∨ False) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184975903522577768041243900330 : (((p4 ∨ (True ∨ p3)) → ((p3 ∨ (p5 ∨ p4)) → (False ∧ False))) ∨ (True ∨ ((((p4 ∨ p5) → (((p1 ∨ p1) → p1) ∧ p4)) → False) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151075948076609943508121128965 : ((((((p1 → p5) → p2) ∧ ((((((p3 ∧ (p1 ∧ False)) → False) ∨ p1) ∧ p5) ∧ p1) ∨ p2)) ∨ p1) → p5) → (p5 ∨ (True → (True ∨ p3)))) := by
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
theorem thm_5_vars_153268309806985077814591601352 : ((False ∨ ((p1 ∨ p4) ∨ ((p4 ∧ ((p3 → (False ∧ (((True ∧ p4) → p1) ∨ (p4 ∧ p4)))) → False)) ∧ True))) → ((p3 ∧ False) ∨ (False → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h6
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134213393634708091509774784102 : (((((True → ((True ∨ (p2 ∨ p4)) ∨ p5)) ∨ p3) → ((p5 → ((p5 ∧ p2) ∨ ((p4 ∨ False) ∨ p2))) ∧ p1)) ∨ p5) ∨ ((p1 → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262414551940028591101129817210 : (True ∧ ((False ∧ (True → (p2 → (p3 ∧ (((p4 ∨ (p5 ∧ False)) ∧ ((p1 ∨ p1) ∧ p2)) ∨ (((False ∧ p1) ∨ True) → (p4 → p5))))))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310667089062301210617003375366 : (p2 ∨ (((True ∨ (False ∧ p5)) → True) → (((p4 ∨ (p3 → (p1 → True))) → (((p3 ∨ p5) ∧ p1) ∧ p5)) → ((p5 ∨ p4) → (p5 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (p4 ∨ (p3 → (p1 → True))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234454939186368996958969900770 : ((p2 → (p5 ∧ p3)) → (((False ∨ p3) ∧ p3) ∨ ((p5 ∧ (False → (True ∧ False))) → ((p4 → p3) ∨ (p2 → ((False ∨ (p4 → True)) ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52155124618665619801467562324 : ((((((p3 ∨ p1) ∨ (False → False)) → ((p1 ∨ p5) ∧ p3)) ∨ (p5 ∧ (p4 ∨ p1))) → (((((False ∨ True) → p5) → p4) → p5) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118239496306026446879743211802 : ((p1 ∨ ((((p5 ∧ (((((True → False) ∧ (False ∨ False)) ∧ p2) → (p3 ∧ False)) ∧ (True → p5))) ∨ False) ∨ p1) ∧ (True ∨ p2))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134035704533275868995588222845 : (((((p4 → (p1 ∨ (((False → p2) ∨ ((p2 ∨ p5) ∨ p5)) ∧ p5))) ∨ (((p1 → p1) ∧ p5) ∨ p4)) ∨ p4) ∨ p2) ∨ (p3 → (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135793140879989488565618389637 : (((((p3 ∧ p5) ∨ p4) → ((p1 ∧ (True ∧ (p4 ∨ (False ∧ p3)))) ∨ p2)) → ((p3 ∧ ((p2 → p3) → True)) ∧ p5)) ∨ ((p2 ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111417320676541023014907828274 : (((p3 ∨ ((p5 ∧ (False ∧ (((p4 ∨ (p1 ∨ p5)) → (p4 ∨ p5)) ∨ p3))) ∨ (((p4 ∧ p4) ∧ (False → True)) → p1))) ∧ p3) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64096077029589655582008021286 : ((False ∨ ((p5 ∨ (p5 ∧ (p2 → (True → ((p5 → p3) ∧ p4))))) ∧ ((p2 ∧ (p1 → True)) ∨ (p5 ∨ ((p3 → (p1 ∧ p3)) ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55258222554753706849446532355 : ((((p5 ∨ False) ∨ (p2 ∧ (p2 ∨ p3))) ∨ (p4 → ((((p2 ∨ p2) ∨ p4) ∨ True) ∨ (True → (((p2 ∨ True) ∧ False) → (p3 ∧ p2)))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321339024780076694134583920843 : (p4 ∨ (p5 ∨ (p4 ∨ ((((p1 ∨ p1) ∨ p4) ∧ ((p3 ∨ (p3 → (p4 ∨ (p3 → (p4 → False))))) ∨ ((False ∨ p3) → (p5 ∧ True)))) ∨ True)))) := by
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
theorem thm_5_vars_255546771104016693774900766178 : ((p5 ∧ p3) → (((p5 ∨ ((True ∧ False) ∧ True)) ∧ (p2 ∨ ((p1 ∨ (True → p1)) → ((False → p3) → (True ∧ ((p2 ∧ False) ∧ True)))))) ∨ True)) := by
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
theorem thm_5_vars_157877730992151865475734381490 : ((((((True ∧ (p3 ∧ p1)) ∨ p2) → p1) → (p5 ∨ False)) ∨ (False ∨ ((p3 ∧ (p5 ∧ p3)) → True))) ∨ (((p2 → (False ∨ p2)) ∧ p1) ∨ p5)) := by
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
theorem thm_5_vars_142424510621426383332902435145 : ((p4 ∧ (p5 ∧ ((p1 → p5) → (((p5 → (p3 ∨ False)) → p1) ∧ (((False ∧ p2) ∧ p3) ∨ (p4 → (False ∧ p1))))))) → (p3 ∧ (p1 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (p1 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- False on the left can always be used.
    apply False.elim h13
  case inr h15 =>
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h17 := h15 h16
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- False on the left can always be used.
    apply False.elim h18
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h19 := h1.left
  let h20 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h20.left
  let h22 := h20.right
  -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
  have h23 : (p1 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h24
    -- One of the premise coincides with the conclusion.
    exact h21
  -- We have shown the premise of h22, we can now drive its conclusion.
  let h25 := h22 h23
  -- We need to get the right conjuct of h25 based on <expert-advice>.
  let h26 := h25.right
  -- Disjunctions on the left can always be decomposed.
  cases h26
  case inl h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h27.left
    let h29 := h27.right
    -- Conjunctions on the left can always be decomposed.
    let h30 := h28.left
    let h31 := h28.right
    -- False on the left can always be used.
    apply False.elim h30
  case inr h32 =>
    -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
    have h33 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h32, we can now drive its conclusion.
    let h34 := h32 h33
    -- We need to get the left conjuct of h34 based on <expert-advice>.
    let h35 := h34.left
    -- False on the left can always be used.
    apply False.elim h35
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789953789453368118046968948308 : (((p5 ∨ ((True ∨ p3) ∧ ((((((p4 → False) → (p5 ∧ p2)) ∧ ((True ∧ True) ∨ p5)) → ((p5 → p4) → (p4 → False))) ∧ p2) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248405583083005770542040223998 : ((p2 ∨ p4) ∨ (((False ∨ (p1 ∧ False)) ∨ (False ∧ True)) ∨ (((p4 ∧ (p4 ∧ ((p3 ∨ (p4 ∨ p3)) ∧ p1))) → p1) ∨ ((p4 ∨ p2) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118477431975886047529281024649 : ((p3 ∨ (((True → p3) ∨ ((((False ∨ p3) ∨ (False ∨ p4)) ∧ ((False ∨ p5) → (p4 ∨ (p4 ∧ p2)))) ∧ p1)) ∧ (True ∧ p1))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149140829489342530567271553692 : (((p5 ∧ p3) ∧ (p1 ∧ (p1 ∨ ((True ∧ ((p1 ∧ (p2 → p2)) ∨ ((False → (p2 ∨ p5)) ∨ p1))) ∧ p1)))) ∨ ((p4 ∨ p3) → (p3 → p3))) := by
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
theorem thm_5_vars_327231184364140445717588868684 : (True → ((p3 → (((False ∧ p1) → p1) → (p2 ∨ ((True ∨ p4) ∧ (((True → (p1 ∧ (p5 ∧ (p2 ∨ (p1 → p5))))) ∨ True) ∧ p3))))) ∨ p5)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264569946799118004554010806213 : (True ∧ ((p1 ∧ (p3 ∨ p5)) ∨ (((p4 ∧ p3) ∨ ((p2 ∨ p2) ∨ ((False ∧ ((p1 → p1) → p4)) → True))) ∨ (p5 ∨ (False ∧ (p2 ∨ p5)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44876050553075206186310142113 : (((((p5 ∨ True) ∧ p1) → (((p4 → p1) ∧ True) ∧ (p4 → ((p2 ∨ (((p3 ∨ p2) ∧ p1) ∧ (p4 → p1))) ∨ (p2 ∧ p3))))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345053787299515918886314174087 : (p3 → ((((True ∨ (p3 ∨ p2)) ∧ (p3 ∨ (p4 → (((True ∧ p2) → ((p2 ∨ (p4 ∧ True)) → p1)) ∨ p1)))) → (p1 → (p2 ∨ p1))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778205420217993769947604637202 : (((p1 ∨ ((True ∨ p3) → (p2 ∧ ((p5 → (p2 ∧ False)) → (p1 ∧ (((p4 ∧ (p3 → (False ∧ ((p2 ∨ p2) ∧ p5)))) ∨ p5) ∨ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118365106086297529499293303316 : ((p2 ∨ (((((p4 ∨ p3) → (p2 ∧ p2)) ∨ p2) ∨ (p5 ∧ ((((p4 ∨ True) → p1) ∨ (True ∨ p4)) → p1))) → (p4 → p3))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669487658562411385279822471743 : ((((((False ∧ (((p5 ∨ (p4 ∧ ((p3 ∨ (True ∨ p4)) → (p2 → True)))) → False) ∧ p1)) → p2) → (p1 → p5)) ∨ ((p3 ∨ p4) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_803345665523494239404385805811 : (((p3 → (((p3 → p5) ∧ (p5 ∧ (((p1 ∧ (p1 ∧ (False ∨ (True ∧ (False ∨ (True → p1)))))) ∧ p5) ∨ ((p1 ∧ False) ∧ True)))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196949750982719344333022966617 : (((((p1 → (p1 → p5)) → p5) ∨ p4) ∨ p2) ∨ ((p1 ∨ False) ∨ (((p5 → ((True ∧ (False ∧ (p2 ∨ True))) ∨ p1)) ∨ p4) → (False → p5)))) := by
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
theorem thm_5_vars_803358400814768534652151029648 : (((p3 → (((p5 ∨ p4) → (((p1 → (((p4 ∧ p1) → True) ∨ p3)) ∧ (((p5 ∧ False) ∨ p2) ∨ p2)) ∨ (p5 → (p3 → True)))) ∨ False)) ∨ False) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354736737582228374596784718541 : (p5 → ((((p1 ∧ (True ∧ (True ∧ (p3 → ((p1 ∨ (((p3 ∧ False) ∨ p1) → False)) ∨ p2))))) ∧ p3) → ((p4 ∨ p4) ∨ (p3 → p2))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41679601712803683927766195127 : (((((p4 → p5) ∨ (p2 ∨ (p3 → False))) ∨ (((p5 → p2) ∨ (p5 → ((p5 ∨ p5) ∧ p3))) → (((False ∨ p1) ∧ p5) ∧ p1))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343403808746202419695621933837 : (p2 → ((p4 ∧ True) ∨ (p4 ∨ ((((p3 ∨ p3) ∧ True) ∨ (((((False ∧ (False ∨ p5)) → p1) ∧ False) ∧ p5) ∨ ((True ∧ p5) ∧ p2))) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254417753604785805726613953576 : ((p2 ∧ p5) → ((((p1 ∨ p4) → (p3 ∨ p1)) → p4) ∨ (p2 → ((((False ∧ (False ∨ (True → ((p1 → p2) → p1)))) ∧ p1) ∧ p5) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197877991991833733836142779903 : ((((p1 ∨ p5) ∨ False) → (p4 ∨ (p4 ∨ False))) ∨ ((((p3 ∨ (False → p1)) → False) → False) ∧ (p2 ∨ ((False ∨ ((True ∧ p1) ∧ False)) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ (False → p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356218332734861496288728261380 : (p5 → (((p1 ∧ (((p2 → p3) ∧ (True ∧ (p1 → (p2 ∨ (p3 ∧ p4))))) ∧ p4)) ∨ True) ∧ ((True → (p1 ∨ ((p5 ∨ p2) ∨ p1))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1567994799243480813231027456 : ((p2 → (p4 ∧ (p5 ∨ (((((p1 ∧ (p2 → p4)) → p4) ∨ p1) → p4) ∨ ((p1 ∧ (p2 ∨ p3)) ∧ (p2 ∧ p2)))))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164733958123407447008628207461 : ((((p3 → (p5 → (((((p4 ∧ p4) ∨ p1) ∨ p3) ∧ (p4 → p4)) ∨ False))) → p4) ∨ p5) ∨ (p3 → (True ∨ ((False ∨ (False ∧ p4)) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316699760381144799348716412073 : (p3 ∨ (p5 ∨ (((p5 ∧ p1) ∧ p4) ∨ ((False ∧ p5) → ((((True ∧ True) ∨ p1) ∧ ((p1 ∧ (True ∧ p2)) → (p2 → (p2 ∧ p3)))) ∨ p1))))) := by
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



