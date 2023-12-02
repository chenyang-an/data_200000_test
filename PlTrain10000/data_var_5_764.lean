variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179221783478340858852450010213 : ((p4 ∧ ((p1 ∧ p1) ∧ (((p5 ∨ p1) → False) ∨ ((True ∧ p3) → p2)))) ∨ ((p3 ∨ (((p5 → p4) ∨ (p2 ∧ (p5 → p4))) ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350262246775419021450303089907 : (p4 → ((p2 ∧ ((p1 → p3) ∧ ((p3 ∧ (p5 ∨ (((((p5 ∨ ((False ∨ p5) → p4)) ∧ p1) ∧ True) ∧ p4) ∨ p3))) → (p3 ∧ False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63944378783250545552601277467 : ((False ∨ ((((p4 ∧ p5) ∨ False) ∨ (((p5 ∧ ((((p2 ∨ p3) ∧ False) ∧ p5) → (p1 ∧ True))) ∨ True) ∨ (p3 ∨ (p2 ∧ True)))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610897685658987129079980688651 : ((((((False → (p5 → ((((p3 ∨ p3) ∧ p4) ∧ (p3 ∨ p3)) → False))) ∨ (False → (True ∧ (p3 ∧ ((False ∨ False) ∨ p5))))) → p3) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184448080184669016189334440296 : (((p4 ∧ (((True ∨ (p5 ∨ p4)) ∨ p3) → p4)) ∧ (p3 ∧ False)) ∨ ((p5 → (((((p2 ∨ False) ∨ True) → True) ∧ (p2 ∨ p2)) → True)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349333019444671977113443027274 : (p3 → (p3 → (((((((p2 ∧ p1) ∧ ((p1 → p4) ∨ (p2 ∧ (((p2 ∧ p2) → p2) ∧ (p3 ∨ p5))))) ∧ True) → p5) ∨ False) ∧ True) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229213650852382989160744097507 : ((True → (p4 → p2)) ∨ (p1 → (((p3 → True) ∧ (p2 ∨ ((((False ∨ p4) → (False ∧ p4)) ∨ p1) → ((p1 ∧ p2) ∧ p4)))) ∨ (False ∨ p1)))) := by
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
theorem thm_5_vars_305000544637725034564269539044 : (p1 ∨ ((((p4 → False) → ((((p2 ∧ (p1 → p5)) ∨ True) → (p2 ∨ p1)) → (p1 ∨ p4))) ∨ (p1 → (False → p1))) ∨ (p5 ∧ (p3 ∨ False)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116414350985674747858267749824 : (((p1 ∨ (p3 → p3)) → (((p4 → ((False → (False → p2)) ∧ ((p5 ∨ True) ∨ False))) → (((False ∨ True) ∧ p1) → p2)) ∧ p5)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677546796044360344563092960328 : (((((p1 ∨ (p4 ∧ ((p1 ∧ ((p2 → ((p3 ∨ (False → True)) ∧ p5)) ∧ (p5 ∧ p5))) ∧ p1))) ∨ p5) ∨ (p4 → (False → (p3 ∧ p4)))) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50118649125650786775670023483 : (((p1 ∨ (p1 ∧ (p4 ∧ (p1 ∨ ((p4 ∨ (((True ∧ (p1 → (p1 ∨ p2))) ∧ p1) ∨ True)) → True))))) ∧ (p5 ∧ (p4 ∧ (False ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190600223890320459714155794592 : ((((False → p3) ∨ ((p2 ∨ (p5 ∨ p1)) → True)) → p3) ∨ ((((p2 ∧ (p5 ∨ (p3 ∧ (p1 ∧ (p1 → p3))))) ∧ p1) → p2) ∨ (p3 ∧ True))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193757678191609672055306193150 : ((p3 ∧ ((p2 ∧ p2) ∨ (True ∨ (p5 ∧ (p4 → p5))))) → (((True ∨ (p3 ∧ p4)) → False) ∨ ((p2 ∧ p4) ∨ (p3 ∨ ((p2 ∧ p5) ∧ p4))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121393271383594551765283996300 : (((((p1 ∨ ((((p3 ∧ p2) ∨ False) ∧ p4) ∧ p2)) ∨ (((p5 ∨ p4) ∨ ((p3 ∨ p5) ∧ p1)) ∨ (False → False))) ∨ True) → p1) → (p1 ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ ((((p3 ∧ p2) ∨ False) ∧ p4) ∧ p2)) ∨ (((p5 ∨ p4) ∨ ((p3 ∨ p5) ∧ p1)) ∨ (False → False))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620383743886604026568001424746 : (((((p3 ∨ p4) ∨ (p4 ∨ (True → (((p1 → False) ∨ ((False → (p3 → True)) ∨ (((p2 ∧ True) ∨ p4) → p1))) ∧ (p2 ∧ False))))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117772418054448937735778094772 : ((p4 ∧ ((p5 ∧ ((p5 ∨ (((((False → (False → p4)) → p5) ∨ p4) → False) ∨ p5)) → (p1 → (p3 ∧ p1)))) ∨ (p3 → False))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117702838001977623400695644136 : ((p3 ∧ (False ∧ (((p2 ∧ (p5 ∨ (p3 → True))) ∧ ((((p5 ∧ p2) ∧ True) → p4) ∧ (p5 → True))) ∧ (p2 ∨ (p5 ∨ p1))))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657295185841647444834740608639 : (((((p2 ∧ p2) ∧ ((((p4 ∨ p4) ∨ (((False ∧ p3) ∧ (((p5 ∧ (p5 ∨ False)) ∧ True) → p5)) ∨ p5)) ∧ p4) ∨ p2)) ∨ (p1 → p1)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136754916011959574757791935573 : (((p2 ∨ p3) ∧ (True ∧ (p3 ∨ ((p3 ∨ p1) ∨ (((p1 ∨ p1) ∧ p4) ∧ ((p1 ∨ (p1 → p1)) → (True ∧ False))))))) ∨ (p3 → (p3 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149851591447340311582844396845 : ((p1 ∨ (p1 ∨ (p5 ∨ (p3 → (((p1 → (((p1 ∨ p3) ∨ (True → True)) ∨ False)) ∧ p4) ∧ (p4 ∨ p1)))))) ∨ ((True → False) → (p4 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206963720969958769586444682867 : ((((p4 ∧ (False → p3)) → p1) ∧ p3) → (((p1 ∧ p3) → ((True → ((p1 → ((True ∧ p3) → p2)) → p3)) ∨ p5)) ∨ (p3 → (False ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759404146504541252190927303384 : (((p2 ∧ (((p4 → (((False → p1) ∧ ((p3 ∧ p1) ∧ p5)) ∨ (((p3 ∧ (p1 → p5)) → p1) ∧ p3))) ∨ False) → (p3 ∨ (p3 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110540174458656570261915912211 : ((p4 → ((p3 ∨ p2) ∨ ((p2 ∨ ((False → False) ∧ (True ∧ True))) → (p5 ∨ (p1 → (p5 ∨ ((p5 ∨ p1) → (p1 ∨ True)))))))) ∧ (p3 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
  -- Implications on the right can always be decomposed.
  intro h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327828900448870231612485606429 : (True → ((((p5 ∨ (p4 → True)) ∨ ((False → (((((p3 ∨ True) ∨ (p4 ∧ p5)) ∨ p4) ∨ p1) → False)) ∨ True)) → (p5 ∨ p2)) ∨ (False → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134718443594964725978806282996 : (((((True ∧ False) → False) ∨ (((p2 ∧ (p3 ∨ False)) → (p1 ∧ (p2 ∨ (p2 ∨ p5)))) ∧ ((True → p1) → p4))) → p1) ∨ (True ∧ (True ∨ p1))) := by
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
theorem thm_5_vars_247526701646549570542901951585 : ((False ∨ p4) ∨ ((p5 ∨ (p4 ∨ (((p2 ∨ ((((p4 → ((p5 ∧ p1) ∨ True)) ∧ (True → (False → p3))) → False) → p3)) → p1) → p1))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ ((((p4 → ((p5 ∧ p1) ∨ True)) ∧ (True → (False → p3))) → False) → p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((p4 → ((p5 ∧ p1) ∨ True)) ∧ (True → (False → p3))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h4
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661448220551742426401393452084 : (((((((p2 ∧ True) ∧ (((p2 ∨ (True → p1)) ∨ False) → (((True ∨ True) → False) ∨ p2))) → False) ∧ ((p3 → p1) ∨ False)) → (False ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159452184800884903730413354904 : (((((p2 ∨ p3) ∨ (((True → (p4 ∧ p1)) ∨ p5) ∧ True)) ∧ (p4 → ((True ∧ False) ∨ p4))) ∧ p4) → (p5 → (((p5 ∨ p2) → p2) ∨ p5))) := by
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
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305778927025772378120327764004 : (p1 ∨ ((True ∧ (p2 ∧ (((p2 ∧ p2) ∧ False) → p2))) ∨ ((False ∧ ((p2 ∧ p5) ∧ False)) ∨ ((p1 ∨ p3) ∨ (((True ∧ p5) ∧ False) → p2))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630670630538436055925183653330 : (((((False → (p2 ∨ ((p1 ∨ (p4 ∧ ((False → ((((p1 ∨ False) ∧ p2) → p4) ∧ ((False ∨ True) ∧ p2))) ∧ False))) ∨ p1))) ∨ p5) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326264336083827700560808019798 : (p5 ∨ (p3 → (p2 ∨ ((p1 → (((p1 ∨ p5) → (True ∨ (True → ((p1 → False) ∧ (True ∨ p3))))) ∧ p5)) ∨ (((p2 ∧ p3) ∨ p1) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_55900614264059084366339608472 : (((p3 ∨ (p1 → (True ∧ p2))) ∧ (p3 ∨ (((((p3 ∧ True) ∨ p3) ∧ p5) ∧ (p1 → p2)) ∨ (p1 ∧ ((False ∧ (p4 ∧ True)) ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_822750331896709615800175215 : ((p4 ∧ ((False ∨ (((((p3 ∧ p3) ∧ ((p1 ∧ False) → p5)) ∧ p3) ∨ (p5 → p4)) ∧ (p4 ∧ ((p4 ∨ False) ∨ False)))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601660709059312615132192978030 : ((((p3 ∧ (False ∨ ((((p1 ∨ (p1 → (p4 → (p3 ∧ False)))) → p2) ∨ p3) ∨ (p3 → ((p1 → True) ∧ (p4 → (p5 → p1))))))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317623836935389406797038128710 : (p4 ∨ ((((((p2 ∨ ((p4 → p5) → (p3 ∨ False))) ∨ (False → ((p3 ∧ (p1 ∨ (p3 ∨ p5))) ∧ p3))) ∨ p4) ∧ (p3 ∨ p3)) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319404676010635180568413205389 : (p4 ∨ (((p5 ∨ p4) ∧ (p1 ∨ ((True ∨ (p1 ∨ p3)) ∧ (p4 ∨ (p5 ∨ p1))))) → (((True ∨ (True ∧ ((p5 ∨ p2) → True))) → False) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    cases h4
    case inl h6 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h7 : (True ∨ (True ∧ ((p5 ∨ p2) → True))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h7
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h14 : (True ∨ (True ∧ ((p5 ∨ p2) → True))) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h15 := h2 h14
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h18 : (True ∨ (True ∧ ((p5 ∨ p2) → True))) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h19 := h2 h18
            -- False on the left can always be used.
            apply False.elim h19
          case inr h20 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h21 : (True ∨ (True ∧ ((p5 ∨ p2) → True))) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h22 := h2 h21
            -- False on the left can always be used.
            apply False.elim h22
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h25 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h26 : (True ∨ (True ∧ ((p5 ∨ p2) → True))) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h27 := h2 h26
            -- False on the left can always be used.
            apply False.elim h27
          case inr h28 =>
            -- Disjunctions on the left can always be decomposed.
            cases h28
            case inl h29 =>
              -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
              have h30 : (True ∨ (True ∧ ((p5 ∨ p2) → True))) := by
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h2, we can now drive its conclusion.
              let h31 := h2 h30
              -- False on the left can always be used.
              apply False.elim h31
            case inr h32 =>
              -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
              have h33 : (True ∨ (True ∧ ((p5 ∨ p2) → True))) := by
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h2, we can now drive its conclusion.
              let h34 := h2 h33
              -- False on the left can always be used.
              apply False.elim h34
        case inr h35 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h36 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h37 : (True ∨ (True ∧ ((p5 ∨ p2) → True))) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h38 := h2 h37
            -- False on the left can always be used.
            apply False.elim h38
          case inr h39 =>
            -- Disjunctions on the left can always be decomposed.
            cases h39
            case inl h40 =>
              -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
              have h41 : (True ∨ (True ∧ ((p5 ∨ p2) → True))) := by
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h2, we can now drive its conclusion.
              let h42 := h2 h41
              -- False on the left can always be used.
              apply False.elim h42
            case inr h43 =>
              -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
              have h44 : (True ∨ (True ∧ ((p5 ∨ p2) → True))) := by
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h2, we can now drive its conclusion.
              let h45 := h2 h44
              -- False on the left can always be used.
              apply False.elim h45
  case inr h46 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h47 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h48 : (True ∨ (True ∧ ((p5 ∨ p2) → True))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h49 := h2 h48
      -- False on the left can always be used.
      apply False.elim h49
    case inr h50 =>
      -- Conjunctions on the left can always be decomposed.
      let h51 := h50.left
      let h52 := h50.right
      -- Disjunctions on the left can always be decomposed.
      cases h51
      case inl h53 =>
        -- Disjunctions on the left can always be decomposed.
        cases h52
        case inl h54 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h55 : (True ∨ (True ∧ ((p5 ∨ p2) → True))) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h56 := h2 h55
          -- False on the left can always be used.
          apply False.elim h56
        case inr h57 =>
          -- Disjunctions on the left can always be decomposed.
          cases h57
          case inl h58 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h59 : (True ∨ (True ∧ ((p5 ∨ p2) → True))) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h60 := h2 h59
            -- False on the left can always be used.
            apply False.elim h60
          case inr h61 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h62 : (True ∨ (True ∧ ((p5 ∨ p2) → True))) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h63 := h2 h62
            -- False on the left can always be used.
            apply False.elim h63
      case inr h64 =>
        -- Disjunctions on the left can always be decomposed.
        cases h64
        case inl h65 =>
          -- Disjunctions on the left can always be decomposed.
          cases h52
          case inl h66 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h67 : (True ∨ (True ∧ ((p5 ∨ p2) → True))) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h68 := h2 h67
            -- False on the left can always be used.
            apply False.elim h68
          case inr h69 =>
            -- Disjunctions on the left can always be decomposed.
            cases h69
            case inl h70 =>
              -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
              have h71 : (True ∨ (True ∧ ((p5 ∨ p2) → True))) := by
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h2, we can now drive its conclusion.
              let h72 := h2 h71
              -- False on the left can always be used.
              apply False.elim h72
            case inr h73 =>
              -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
              have h74 : (True ∨ (True ∧ ((p5 ∨ p2) → True))) := by
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h2, we can now drive its conclusion.
              let h75 := h2 h74
              -- False on the left can always be used.
              apply False.elim h75
        case inr h76 =>
          -- Disjunctions on the left can always be decomposed.
          cases h52
          case inl h77 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h78 : (True ∨ (True ∧ ((p5 ∨ p2) → True))) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h79 := h2 h78
            -- False on the left can always be used.
            apply False.elim h79
          case inr h80 =>
            -- Disjunctions on the left can always be decomposed.
            cases h80
            case inl h81 =>
              -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
              have h82 : (True ∨ (True ∧ ((p5 ∨ p2) → True))) := by
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h2, we can now drive its conclusion.
              let h83 := h2 h82
              -- False on the left can always be used.
              apply False.elim h83
            case inr h84 =>
              -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
              have h85 : (True ∨ (True ∧ ((p5 ∨ p2) → True))) := by
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h2, we can now drive its conclusion.
              let h86 := h2 h85
              -- False on the left can always be used.
              apply False.elim h86



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121566677101103848751239660071 : (((((p4 ∨ True) → (((True ∨ (((p1 → True) ∨ (p2 ∧ p3)) ∧ p3)) ∧ (p5 → (False → p1))) ∧ False)) → (p1 ∧ p4)) → False) → (p5 → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p4 ∨ True) → (((True ∨ (((p1 → True) ∨ (p2 ∧ p3)) ∧ p3)) ∧ (p5 → (False → p1))) ∧ False)) → (p1 ∧ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p4 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : (p4 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h3
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668844110391922499307257446294 : (((((((p5 ∧ ((False → p3) ∨ p4)) ∨ p3) → ((p5 ∨ p5) ∧ (((p2 ∨ (True → p2)) ∧ p5) → False))) ∨ True) ∨ ((True ∨ p3) → p1)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_56585880418554067073933040041 : (((p1 → (p1 → (p3 ∧ p2))) → ((p4 ∨ (p3 ∧ p5)) ∨ (((p3 ∨ (p2 → p1)) ∨ (p4 ∧ (False ∨ p1))) → ((p3 ∧ p5) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67637495228732659381299013102 : ((p1 → (False ∨ ((p2 ∧ False) ∨ ((((((p4 ∨ (p2 → p5)) ∧ p4) → (p4 ∧ p3)) ∨ True) ∧ ((p4 ∨ True) → p3)) ∨ (p4 → p4))))) ∨ p5) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40677781349681913664570118591 : ((((((((True → p3) ∨ (False ∨ (p5 → True))) ∧ p1) ∧ (p5 ∧ ((p4 ∨ p2) → (p2 ∨ False)))) ∨ (True → (False ∨ p4))) → p4) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199777878096180579581182325258 : (((p4 → ((p1 ∨ p5) ∨ (p5 → p4))) → False) → (p2 ∨ ((p5 ∧ False) ∨ (p2 → ((p5 ∨ p3) ∧ (((p4 ∧ p3) → p2) → (p2 → p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → ((p1 ∨ p5) ∨ (p5 → p4))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680585696691239324374115316415 : (((((p1 ∨ (((p2 ∨ p1) ∧ False) → (p1 ∨ True))) ∨ ((p5 → False) ∧ (p2 ∧ (p2 → (p1 → p2))))) → (p2 ∨ (p2 ∨ (p5 ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621812751127317396006622408027 : ((((p1 ∧ ((False ∨ (((p2 ∨ False) ∨ (False ∨ (p2 ∨ ((True ∧ p4) ∧ (p1 ∨ (p2 ∨ False)))))) → p4)) ∧ (p3 ∧ (p5 ∧ p1)))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41245361036939802733959439462 : ((((((((p3 ∧ p2) → ((True ∨ (False ∨ (p1 → (p3 → False)))) ∧ p2)) → True) → p3) ∨ p3) ∨ (False ∨ ((p5 → p4) ∧ p5))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342741939333529668723110503885 : (p2 → (((((p1 ∧ p3) ∨ (p1 → p4)) ∨ p5) ∧ False) ∨ (((p1 → (((p3 ∨ (p2 ∨ (p4 ∧ p4))) ∨ p2) ∨ p2)) ∨ (p4 ∧ p1)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313946180188429639469245742920 : (p3 ∨ ((((p1 ∧ (p3 ∨ (p2 ∨ ((p3 → True) ∨ False)))) ∧ (p2 ∨ (p2 ∨ ((True ∨ p4) → (True ∨ (p3 ∨ False)))))) → p3) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246335334774034095807989566107 : ((p4 ∧ p5) ∨ (((p1 ∧ (p1 ∧ ((p3 ∨ p3) ∧ ((True → True) ∧ p5)))) ∧ (p5 ∨ p5)) ∨ ((True ∧ p5) → (p4 → ((p5 → p3) → p4))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259543013478661355404717143185 : ((False → p5) → (p2 → ((False ∨ (((((((p2 → p3) → (p1 → (True ∧ (p4 → (p2 → p3))))) ∨ False) → p3) ∨ p4) ∧ p3) ∨ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113727549175625995516016918924 : ((((((False ∧ (p1 ∨ ((p5 ∧ p5) ∨ (p4 → p4)))) ∧ (False → False)) → (p2 ∨ p5)) ∨ ((p3 ∨ p2) ∧ p3)) → (p3 → False)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157938272598689435530414193366 : (((((False → p3) ∨ p5) → ((p2 → False) ∧ p3)) ∧ ((p2 → ((False ∨ p4) ∧ p5)) ∧ (p5 ∧ False))) ∨ (p5 → ((p3 ∨ p5) → (p1 → True)))) := by
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
theorem thm_5_vars_644276962938844975464234581596 : ((((False ∨ ((True ∨ (p3 ∧ ((True ∨ ((p5 → True) ∨ ((True ∨ False) ∧ p2))) → ((False → (True ∧ p1)) ∨ p5)))) ∧ (True ∨ False))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65181318241958334117843895220 : ((p3 ∨ (((False → (p3 ∧ True)) → ((((((p3 ∨ p4) ∨ p3) → False) ∨ ((p5 → True) → (True ∧ p3))) ∧ (True ∧ p4)) ∨ True)) ∧ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_588270992376478788904077486845 : ((((((((True ∨ p5) ∧ p5) ∧ (False → p1)) ∨ ((False ∨ (p3 ∨ (((p4 → p3) → p3) ∨ False))) → (True ∧ (p4 ∨ p5)))) ∨ p3) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715059050277490915273936137801 : ((((p2 ∨ (p3 ∨ (p4 ∧ (p5 ∧ p5)))) → ((p3 → p1) ∧ (((((p2 → True) ∧ (p4 ∨ (False ∨ p4))) ∨ True) → p5) ∨ (False ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62862798980590524990054182951 : ((p4 ∧ (((p4 → p2) ∨ p1) ∧ ((((p5 → False) → (((p4 → (True → (p2 ∨ p3))) ∧ p2) ∨ p4)) → p4) ∨ ((False → p3) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731141548822887900533315723782 : ((((p2 ∨ (p5 ∧ p5)) → ((p3 → ((((p4 ∧ (p4 ∨ False)) ∨ (p4 ∨ ((p1 ∨ p5) → False))) ∨ False) ∨ (True → True))) ∧ (False → True))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h9
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178735962355806014344583145984 : (((True ∧ (p4 → (p4 → p2))) → (p4 ∨ (p5 → (p1 ∨ (p2 → p4))))) ∨ ((False ∧ p1) → (False ∨ (p4 ∧ (p3 → ((p4 ∧ False) → p4)))))) := by
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
theorem thm_5_vars_339736737418412769898060425218 : (p1 → (p4 ∨ ((True → (((True ∧ (((p3 → True) → False) → ((p4 ∨ (p4 ∧ p4)) ∧ False))) ∨ ((p4 → False) → p4)) ∨ True)) ∨ (p2 ∨ p5)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167593590247150066425875493532 : (((p2 ∧ ((((False ∨ (False → (p4 → True))) → (p3 → p3)) ∧ p2) → p4)) ∨ (True ∧ False)) → (((p5 ∧ True) ∨ ((p2 ∨ p1) ∧ p3)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (((False ∨ (False → (p4 → True))) → (p3 → p3)) ∧ p2) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179199919656644675362383279053 : ((p3 ∧ (p2 ∨ (False ∨ (((False ∨ p4) → (False ∨ False)) ∨ (p3 ∧ p3))))) ∨ ((p5 ∨ p3) ∨ (p2 ∨ ((p1 → p4) ∨ ((False → False) ∨ p2))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263140768619967186726004933228 : (True ∧ (((True ∧ p1) ∧ (((p5 ∧ False) ∧ ((True → p2) ∧ p5)) ∨ (((p1 ∧ ((p5 ∨ (p4 ∨ p4)) ∨ False)) ∨ True) ∨ True))) ∨ (True ∨ p4))) := by
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
theorem thm_5_vars_184650228341253305222217471425 : (((((p2 ∨ (p1 → True)) → p1) ∨ p3) ∨ ((True ∨ p5) → p2)) ∨ ((((True → ((p2 ∨ p3) ∨ p2)) ∨ p3) → True) ∨ ((p4 → p2) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351524369840499231581576209918 : (p4 → (((((p2 → p5) → p5) ∨ (p4 ∧ ((p3 ∨ (p3 → p1)) → (p5 ∧ (p1 ∨ p3))))) → p2) ∨ (False ∨ (((p1 → p3) ∧ p1) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_14704749387938377595662822813 : (((((p3 → (p4 → True)) ∧ (p4 ∧ ((p5 ∨ (((p3 → ((False ∧ p2) ∨ p1)) → p5) ∨ True)) ∧ p1))) ∨ (False → False)) ∨ (p3 → True)) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212318977099444614119454517805 : ((p1 ∨ (True ∨ (p2 ∨ p2))) ∧ (((p3 → True) ∧ p4) → (((((True ∧ p5) ∨ p4) ∧ True) → ((((False ∨ p1) ∨ p1) ∨ False) ∨ p2)) ∨ True))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113020920565028923587823473959 : (((p5 ∧ (p3 → ((((True ∧ (p2 → p1)) → p2) ∧ ((True ∧ ((p4 → (True ∧ p2)) ∧ False)) ∨ (p2 ∧ p5))) ∨ False))) → p4) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263524659560068406399234662894 : (True ∧ (((((p3 → p5) ∧ (True → False)) ∧ p5) → (False ∧ (p1 → ((((p1 ∨ False) ∨ p5) → False) ∧ False)))) ∧ ((p5 ∧ p2) → (False → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h9
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h1.left
      let h13 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h17 := h15 h16
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h1.left
    let h21 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h24 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h25 := h23 h24
    -- False on the left can always be used.
    apply False.elim h25
  -- Conjunctions on the left can always be decomposed.
  let h26 := h1.left
  let h27 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h28 := h26.left
  let h29 := h26.right
  -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
  have h30 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h29, we can now drive its conclusion.
  let h31 := h29 h30
  -- False on the left can always be used.
  apply False.elim h31
  -- Implications on the right can always be decomposed.
  intro h32
  -- Implications on the right can always be decomposed.
  intro h33
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682607328472746822800021809547 : (((((((p4 → p1) ∨ p4) → (p3 → (False ∧ p4))) ∨ ((p5 → (False → p3)) ∧ (p5 ∧ p5))) ∧ ((((True ∨ p3) → p1) → True) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115286840541849177392453155688 : (((((p1 ∨ (p5 → (p4 ∨ (p2 ∨ True)))) ∨ p5) ∧ p5) → ((((p1 → False) ∧ p1) ∧ p5) → (((p4 ∧ p4) ∧ p3) ∧ p5))) ∨ (p2 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h11 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h12 := h5 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h14 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h15 := h5 h14
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h17 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h18 := h5 h17
    -- False on the left can always be used.
    apply False.elim h18
  -- Conjunctions on the left can always be decomposed.
  let h19 := h2.left
  let h20 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h19.left
  let h22 := h19.right
  -- Conjunctions on the left can always be decomposed.
  let h23 := h1.left
  let h24 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h23
  case inl h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h27 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h26
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h28 := h21 h27
      -- False on the left can always be used.
      apply False.elim h28
    case inr h29 =>
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h30 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h31 := h21 h30
      -- False on the left can always be used.
      apply False.elim h31
  case inr h32 =>
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h33 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h22
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h34 := h21 h33
    -- False on the left can always be used.
    apply False.elim h34
  -- Conjunctions on the left can always be decomposed.
  let h35 := h2.left
  let h36 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h37 := h35.left
  let h38 := h35.right
  -- Conjunctions on the left can always be decomposed.
  let h39 := h1.left
  let h40 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h39
  case inl h41 =>
    -- Disjunctions on the left can always be decomposed.
    cases h41
    case inl h42 =>
      -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
      have h43 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h42
      -- We have shown the premise of h37, we can now drive its conclusion.
      let h44 := h37 h43
      -- False on the left can always be used.
      apply False.elim h44
    case inr h45 =>
      -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
      have h46 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h38
      -- We have shown the premise of h37, we can now drive its conclusion.
      let h47 := h37 h46
      -- False on the left can always be used.
      apply False.elim h47
  case inr h48 =>
    -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
    have h49 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h38
    -- We have shown the premise of h37, we can now drive its conclusion.
    let h50 := h37 h49
    -- False on the left can always be used.
    apply False.elim h50
  -- Conjunctions on the left can always be decomposed.
  let h51 := h2.left
  let h52 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h53 := h51.left
  let h54 := h51.right
  -- Conjunctions on the left can always be decomposed.
  let h55 := h1.left
  let h56 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h55
  case inl h57 =>
    -- Disjunctions on the left can always be decomposed.
    cases h57
    case inl h58 =>
      -- One of the premise coincides with the conclusion.
      exact h56
    case inr h59 =>
      -- One of the premise coincides with the conclusion.
      exact h56
  case inr h60 =>
    -- One of the premise coincides with the conclusion.
    exact h56



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113545479988561376400964966132 : ((((True ∧ (p5 ∨ p4)) ∧ (((p5 ∧ ((False ∧ p4) ∨ True)) → True) → ((True ∨ ((p5 ∨ p5) ∧ p2)) ∧ p2))) ∨ (p3 → p3)) ∨ (True ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152700027876728800746862986948 : (((p4 ∧ p1) ∨ ((((False → (((p1 ∨ p2) → p2) → (p4 ∧ False))) ∨ p5) → True) ∧ ((True → p4) ∨ p1))) → ((p3 ∧ p3) ∨ (p3 ∨ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302527663847365709153062004382 : (False ∨ (False ∨ ((p5 ∨ (p3 → False)) ∨ ((p2 ∨ p3) → (((p4 ∧ False) ∨ p3) → ((False ∧ False) ∨ ((p3 ∨ True) → (False → (True ∨ p3))))))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739331942367509908782914889676 : ((((p4 ∧ p4) ∨ ((p1 ∧ ((p2 → True) → (((((False ∨ True) ∧ p4) ∨ False) ∨ ((p2 → ((p5 ∧ False) ∨ p4)) ∨ p1)) ∧ p4))) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_40078356883204306446205483674 : (((((((p1 ∧ (((False → (p5 ∨ True)) ∨ False) ∧ ((p3 → (True → p3)) → (p3 → (False → p5))))) ∨ p5) → False) → p3) ∧ p1) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42314355541672416939677704586 : (((p2 ∧ ((p3 ∧ p1) ∧ (((((False ∧ ((((((p2 ∨ True) → p5) ∧ p4) ∨ p3) ∧ p3) → True)) ∧ p4) ∨ False) ∧ p4) ∧ p1))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624735488424633276053969313813 : ((((p4 ∨ (p4 → ((((p5 ∨ ((False ∧ (((p2 → p5) ∨ True) → True)) ∨ p2)) ∧ p5) → False) → (p5 ∨ ((p2 → p1) ∨ False))))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355583714933987201569443227650 : (p5 → ((((p5 ∧ (((p2 → (p4 → p2)) ∧ p1) ∧ p2)) ∧ p4) ∧ (p5 → (((False ∨ (p2 ∧ p1)) ∨ (p3 → False)) ∧ True))) ∨ (p5 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221017866247803097665672396502 : (((p3 ∧ p3) ∨ True) ∧ ((p4 ∧ (((p3 ∨ p3) → (p1 ∨ p2)) → ((p2 → (p5 ∨ p5)) ∧ (True ∧ (p1 ∧ (False ∧ True)))))) ∨ (True ∨ p4))) := by
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
theorem thm_5_vars_309344755892227881755593599878 : (p2 ∨ (((((p3 → False) ∨ ((False ∧ (((p4 ∨ (p4 ∨ p3)) ∧ p1) ∧ False)) ∨ p2)) ∨ True) ∨ ((False ∨ (p1 ∧ p5)) ∨ p3)) ∨ (True → p4))) := by
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
theorem thm_5_vars_199046752224174325507579830735 : (((((True → p1) ∨ (p1 ∨ p5)) ∨ p3) ∧ p5) → (((p2 ∨ (p2 ∧ p2)) ∨ (True ∨ ((p1 → p4) → False))) ∨ ((True → p4) ∨ (p2 → True)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116778239984616790284477217438 : (((False ∨ p5) ∨ (((p4 → (False → (((p2 ∧ False) ∧ True) ∨ (((False ∧ p5) ∨ (False → False)) → p2)))) → (p3 → False)) ∨ p3)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205472653196429134902344734252 : (((p5 → (p3 ∧ False)) → (p1 ∧ p1)) ∨ (((p1 ∧ (True ∨ p5)) ∨ False) ∨ ((((p1 → p1) → False) → (p4 → False)) → ((False ∧ False) → False)))) := by
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
theorem thm_5_vars_168331049276832464072322669221 : (((p4 → p4) ∧ (True → (((p3 → (p5 ∨ (p5 ∧ (True → (p2 → p3))))) ∧ p2) ∧ p3))) → ((p1 ∧ ((p5 ∨ (p1 → p3)) ∧ p1)) → p5)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h13 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h14 := h10 h13
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h15 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h16 := h12 h15
    -- We need to get the left conjuct of h16 based on <expert-advice>.
    let h17 := h16.left
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h19 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h20 := h18 h19
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- One of the premise coincides with the conclusion.
      exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57860897135729303836136275905 : (((False ∨ (True ∨ p3)) → (((((((((p4 → (True → False)) ∨ p3) → p2) → p4) ∧ ((True ∧ True) → p1)) → p4) → p5) ∧ True) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112559055726883587416829817548 : ((((True ∧ (((p2 ∧ ((((p5 → p1) ∧ p5) ∨ p3) → p5)) → (((p2 ∧ p3) ∨ False) ∧ p5)) → (False ∧ False))) → True) → p4) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50788362189649968457192152064 : (((p5 ∨ (((p3 ∨ p4) → (((p5 ∨ p2) ∨ p5) → (((p4 → p3) ∧ p5) ∨ (False → p1)))) → p5)) → (((p3 → p1) → p5) ∨ False)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : ((p3 ∨ p4) → (((p5 ∨ p2) ∨ p5) → (((p4 → p3) ∧ p5) ∨ (False → p1)))) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
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
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h17
            -- False on the left can always be used.
            apply False.elim h17
          case inr h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h19
            -- False on the left can always be used.
            apply False.elim h19
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h22
          -- False on the left can always be used.
          apply False.elim h22
        case inr h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h24
          -- False on the left can always be used.
          apply False.elim h24
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h25 := h4 h6
    -- One of the premise coincides with the conclusion.
    exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197510693629809600961145645658 : (((p5 ∨ (p3 → (p1 ∧ p5))) ∧ (p1 → p5)) ∨ ((((((p3 → p4) → p5) ∨ (((False → p1) ∨ p5) → p5)) ∧ (p4 ∨ p1)) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638093766082946518878881871264 : (((((p5 ∨ ((((True ∧ p3) → False) ∧ p5) ∧ p2)) ∨ (p1 ∨ (p1 ∧ (((p4 ∨ (p5 ∨ (p1 → p4))) → p1) → (p5 → p4))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324748242328182718799029940899 : (p5 ∨ ((p2 ∨ (p3 ∨ p1)) → ((((p5 ∧ (False ∨ True)) ∨ p4) ∨ ((p2 → p4) ∨ p4)) ∨ ((p1 → (False → (p1 ∧ p1))) ∨ (p4 ∧ p3))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h8
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h11
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184824644153536260049317914150 : (((((False → True) → p3) → p5) → (p2 ∨ ((p4 → p2) → p2))) ∨ ((p1 → (((p1 → (p4 ∨ (p3 ∨ False))) → (p2 ∧ p5)) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50179153387970258788171711465 : ((((((p2 ∧ False) ∧ (p1 ∧ (((True → (p5 → True)) → (p1 → p2)) ∨ p3))) ∨ (p4 ∨ p3)) ∧ False) ∨ ((True ∨ p1) ∨ (True → p3))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217206635610477899671069645529 : ((((p5 ∨ p3) → p2) ∨ True) → ((p3 → p1) ∨ (p3 → (((((((p2 → p2) ∧ True) ∧ (p5 ∨ p3)) → p2) → (p3 ∨ p5)) → False) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111851724243882070990557424899 : (((((p5 ∧ (p2 ∧ p4)) ∨ (True ∨ (p5 ∨ ((True ∨ p1) → ((p4 → p2) → (p5 ∧ True)))))) → ((False ∨ p2) → p4)) ∨ False) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43862624446386486264038706223 : ((((((((p5 → (p5 ∧ p5)) ∨ p3) → False) ∧ p1) ∧ ((p3 ∧ True) ∨ (p2 → ((p5 ∨ (p4 ∨ p3)) ∨ p4)))) ∧ (p4 ∧ p5)) → p2) ∨ p3) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h3.left
    let h12 := h3.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h13 : ((p5 → (p5 ∧ p5)) ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h14 := h6 h13
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h3.left
    let h17 := h3.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h18 : ((p5 → (p5 ∧ p5)) ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h19
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h19
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h20 := h6 h18
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193305197464223583166201351693 : (((p2 ∧ (p3 → p1)) ∨ ((p4 → False) → (p3 ∧ p4))) → ((((True → (((p3 ∨ ((p3 ∨ p4) → p5)) → p1) ∧ False)) ∧ p3) ∨ False) → p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h11 := h4 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52898074622785828194236806195 : (((p5 ∨ (p5 ∨ (((((p2 ∧ p2) → (False ∨ p4)) ∧ p2) → p2) ∨ p2))) → ((((((True ∧ p1) ∨ p5) ∨ p2) → p2) ∧ p2) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234790127836950453596031553633 : ((p5 → (p2 ∧ False)) → (p3 ∨ (((p1 ∧ p5) ∧ p2) → (((p5 ∨ (((((p2 ∨ p2) → p4) ∨ p3) ∧ p5) ∨ (p5 ∧ p3))) → p4) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h2.left
        let h18 := h2.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h17.left
        let h20 := h17.right
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h21 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h20
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h22 := h1 h21
        -- We need to get the right conjuct of h22 based on <expert-advice>.
        let h23 := h22.right
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h2.left
        let h26 := h2.right
        -- Conjunctions on the left can always be decomposed.
        let h27 := h25.left
        let h28 := h25.right
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h29 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h28
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h30 := h1 h29
        -- We need to get the right conjuct of h30 based on <expert-advice>.
        let h31 := h30.right
        -- False on the left can always be used.
        apply False.elim h31
    case inr h32 =>
      -- Conjunctions on the left can always be decomposed.
      let h33 := h32.left
      let h34 := h32.right
      -- Conjunctions on the left can always be decomposed.
      let h35 := h2.left
      let h36 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h37 := h35.left
      let h38 := h35.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h39 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h38
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h40 := h1 h39
      -- We need to get the right conjuct of h40 based on <expert-advice>.
      let h41 := h40.right
      -- False on the left can always be used.
      apply False.elim h41
  -- Conjunctions on the left can always be decomposed.
  let h42 := h2.left
  let h43 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h44 := h42.left
  let h45 := h42.right
  -- One of the premise coincides with the conclusion.
  exact h43



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354943465622295856042695719103 : (p5 → ((True → (((p3 ∧ (((p2 ∧ p3) ∨ p5) ∧ (((False → False) → (p2 → p2)) ∧ (True ∧ ((p1 → p3) → False))))) ∧ p2) ∧ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117260360486990480684240786141 : ((True ∧ (p5 → ((((False → (((p2 ∨ False) → p2) → ((p3 ∧ ((p2 ∧ p3) ∨ False)) ∨ p2))) ∨ p1) ∨ True) → (p2 → p1)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



