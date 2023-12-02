variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241563292406541609997949729788 : ((False → p3) ∧ (p4 ∨ (((p5 → (False ∧ ((False ∧ p1) ∧ p4))) ∨ p1) ∨ ((p3 ∧ (p4 ∨ (((p4 ∨ (True → p3)) → p5) → p4))) → p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184516474036877230550148983138 : (((p5 ∧ (p4 ∧ (p4 ∨ (p2 → (p1 ∧ p5))))) ∨ (p3 ∧ True)) ∨ ((p5 ∧ False) → ((p3 ∨ (p1 ∨ (p1 → (p1 ∧ (p4 → p3))))) → p1))) := by
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
    let h4 := h1.left
    let h5 := h1.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h1.left
      let h12 := h1.right
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43192516230622793321325767267 : (((((p3 ∨ p2) → (((p1 ∨ (p3 ∧ (p4 ∨ (p5 ∧ (True ∨ (p1 ∧ (p5 ∧ (True ∨ p3)))))))) ∧ False) ∧ (p4 → p2))) ∧ True) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305065078231030206172966972005 : (p1 ∨ ((((((p1 ∨ p1) ∨ p2) → ((p3 ∨ (((p3 ∨ p5) ∨ p1) → p3)) ∨ p1)) ∨ p5) ∧ (False → (True → True))) → (p4 ∨ (p3 ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723355458685183958041377562341 : (((((False ∧ False) → p2) ∧ ((True ∨ True) → ((((((False → p4) ∨ (p2 ∨ p2)) → (p3 ∨ p4)) ∨ ((p5 ∧ True) → p2)) → p3) ∨ True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_893617642301414090656271974550 : (((((True → (False ∨ False)) ∧ (p3 → ((True ∨ (True ∨ (p5 → False))) ∧ ((True → p3) ∨ ((p5 ∧ p3) ∧ p4))))) ∧ (p5 → (True ∨ p4))) → p3) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40822972556443712554050780574 : ((((True → (((((p4 ∧ p5) → (p5 ∨ (((((False → True) → (p1 → p1)) ∧ True) ∧ p3) ∨ True))) ∧ p4) → False) ∨ p5)) → p5) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41562200171238465763867636053 : ((((((p4 ∨ False) ∨ p4) ∧ ((False ∨ (p5 → p5)) → False)) → ((((p5 ∨ p3) ∧ (p1 → (p4 → (p4 → p1)))) ∧ p1) ∨ True)) ∨ p3) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204387064053993779776578101417 : (((True → ((p5 → p4) ∨ p1)) ∧ False) ∨ ((p5 → p1) → ((p1 ∨ ((p3 ∧ p1) ∧ (True → p4))) ∨ ((((p5 ∧ p1) ∧ p1) ∧ True) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66369305384171809322728721015 : ((p5 ∨ (p1 ∨ (p1 → ((False ∨ (False ∨ ((p2 ∨ ((p5 ∧ True) ∧ True)) ∨ True))) ∨ ((p2 ∧ p2) ∨ ((p4 ∧ True) ∨ (p3 ∧ True))))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49029083528445279917217972457 : (((((p5 ∨ (p3 ∧ p3)) ∧ (False ∨ ((p3 ∧ (p1 → p1)) → (p4 ∧ ((False → False) ∧ (p3 ∧ False)))))) → p3) ∨ ((p3 ∨ p3) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149288184737734769358440328438 : (((p3 → p4) ∨ ((((p5 → True) ∨ True) → p5) → ((False ∨ (((p3 ∨ True) → (True → False)) ∧ p5)) ∨ p5))) ∨ ((p5 ∨ p5) ∨ (True ∧ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 → True) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172987673809191504569536044248 : ((p5 ∧ (((((p1 ∧ p2) → p3) → ((p1 → (p1 ∧ p4)) → False)) ∧ p4) ∨ p5)) ∨ ((False → (p5 → False)) → (p5 → ((p2 ∧ p3) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148026438233127054539103336120 : ((((p3 ∨ (p1 ∨ (False → p1))) ∧ (((True → ((p1 → p5) ∧ p3)) → (p1 ∧ False)) ∧ p5)) ∨ (p4 ∧ True)) ∨ ((False → p1) → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53980424791073312723579651739 : (((((p5 ∧ (False ∧ (False ∧ (p3 ∧ p5)))) ∨ p4) ∨ p3) → ((False ∧ ((p3 ∨ True) ∧ (False ∨ False))) ∨ (((p2 ∨ True) ∨ p1) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305161483740843752858783741264 : (p1 ∨ (((p1 ∧ ((p2 → (p3 → ((((p4 ∨ (p5 → p3)) ∨ (False ∨ False)) → p5) ∧ p2))) ∨ p2)) ∨ True) ∨ ((p5 ∨ (p1 ∧ p2)) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662693447348351122943475606419 : ((((((p4 → (p4 ∨ True)) → True) ∨ (False → ((((p2 → p3) → p5) ∧ (p2 → (True → ((p4 → p5) ∨ p4)))) ∧ False))) → (p1 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310401467173855268838858500119 : (p2 ∨ (((p3 → p3) → (((p3 → p5) → p2) ∨ p5)) ∨ (((True ∨ (True → ((False ∨ True) ∨ (True → (p2 ∧ (p1 ∨ True)))))) ∨ p1) ∨ p3))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32489394661870777770996333526 : ((p2 ∨ (((((((p5 ∨ p5) ∧ p3) ∨ p2) ∧ False) ∧ ((p2 → True) → (((p1 → p2) → (p5 ∧ p1)) ∨ p2))) ∨ True) ∧ (True ∨ p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750450104476155229590387002311 : (((True ∧ (((((p2 ∨ False) ∨ True) → p5) → ((((p1 ∨ p3) → p5) ∧ ((p5 ∨ True) → (p3 ∨ p5))) ∨ p5)) ∨ ((p2 → False) ∨ False))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∨ False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71211802906492558690815284413 : (((((p1 ∨ True) → False) ∧ (((True ∨ (True → ((p2 → p4) ∧ True))) ∧ (p4 ∧ (p2 → p3))) ∨ (p2 ∨ (p5 ∨ (p5 → p2))))) ∧ True) → p3) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h12 : (p1 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h13 := h4 h12
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h8.left
      let h16 := h8.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h17 : (p1 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h18 := h4 h17
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h21 : (p1 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h22 := h4 h21
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h25 : (p1 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h26 := h4 h25
        -- False on the left can always be used.
        apply False.elim h26
      case inr h27 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h28 : (p1 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h29 := h4 h28
        -- False on the left can always be used.
        apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165851408755581823286400201781 : ((((False → p5) → False) ∨ (p2 ∨ ((((p4 ∧ ((p4 ∨ True) → p2)) → p2) ∨ p4) ∧ True))) ∨ ((p2 → (((p1 ∨ False) ∨ p2) → p2)) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p4 ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160059493997301827486213136762 : (((p2 ∧ ((((p1 ∨ p5) → (False ∧ (p5 ∨ (p3 ∨ p5)))) ∧ ((p2 → True) → p2)) → p5)) → p4) → (((p2 ∧ p4) ∨ p3) ∨ (True ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301868486407605129080256966631 : (False ∨ ((p2 → p5) ∨ ((p3 → (p1 ∨ p3)) → (p3 ∨ ((((p3 ∨ ((p3 ∧ (p2 ∧ (True ∨ True))) → (p1 ∧ False))) ∨ p2) ∧ True) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65102446155535333223531276717 : ((p2 ∨ (p3 ∨ ((p5 ∨ ((p1 → (p4 ∧ p2)) ∨ (p3 ∨ (((p3 ∧ p4) → p3) ∨ False)))) ∧ (((p2 ∧ False) ∨ p3) → (p4 ∨ p3))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114013008343545475821897053801 : ((((p4 → (((p3 ∧ (p1 ∨ True)) ∨ p2) ∧ ((((False → p3) → p4) → p1) ∨ (p2 ∧ True)))) ∧ False) ∨ ((p5 → p2) ∨ p4)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773447018474514259433808247851 : (((False ∨ ((((p1 → (False ∨ False)) → (p1 ∨ ((((p5 → ((p2 ∨ p3) ∧ p4)) ∧ p1) → (p5 ∨ p2)) → (p3 ∧ p1)))) ∨ p4) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_137931418194687411442750206986 : ((p4 ∨ (p2 ∨ (p2 ∧ ((((p2 ∧ (p3 ∨ (((True ∧ ((p4 ∧ p3) → p5)) ∧ False) → p1))) ∧ p1) → False) → p1)))) ∨ (False → (p5 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114289142269500159423405205850 : ((((p3 → (((p5 → (True ∧ False)) → ((p1 ∧ ((p2 ∧ False) ∧ True)) ∧ True)) → p1)) → p2) ∧ (p1 ∧ (True ∧ (p4 ∧ p3)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184862483351597373851525084970 : ((((p2 ∨ p1) ∨ False) ∧ ((p3 ∨ (False ∨ p3)) ∨ (p3 → False))) ∨ ((((False ∨ p3) → (p4 ∨ ((p2 ∨ (p3 ∨ p5)) → p1))) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779415153300770837944131579527 : (((p2 ∨ ((((p5 → ((True → (p5 → ((p5 → ((p5 ∧ (p3 ∨ p1)) ∨ p1)) → (False ∨ (p4 ∨ p2))))) ∧ p4)) → p2) → p2) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_789750410403054539551518355446 : (((p5 ∨ (((p2 ∨ True) → (True ∧ False)) ∨ (p3 ∨ (((((p4 ∨ p5) ∨ True) ∨ ((p5 → (p1 → (p2 → p3))) ∨ p2)) ∨ p1) ∨ p5)))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_703855169402344030085461898815 : ((((((((True ∧ p1) ∨ p5) ∨ p3) ∨ (True ∧ True)) ∨ True) → (((p2 ∨ p1) → (p5 → ((False ∧ True) ∨ True))) ∨ (p1 ∨ (p5 ∨ p4)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h5 =>
          -- Conjunctions on the left can always be decomposed.
          let h6 := h5.left
          let h7 := h5.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h8
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h21 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h22
    -- Implications on the right can always be decomposed.
    intro h23
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89131737880464826494436468262 : ((((False ∧ False) → p4) ∧ (((((((p2 ∧ ((p3 ∧ True) ∨ p3)) ∨ True) → p4) → (False → p3)) ∨ p5) → p2) ∧ ((p4 ∧ False) → False))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (((((p2 ∧ ((p3 ∧ True) ∨ p3)) ∨ True) → p4) → (False → p3)) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178738039466225014120315265715 : (((p3 ∧ ((p1 ∨ True) ∨ True)) → ((p2 ∨ (p3 → p1)) ∨ (False ∧ p2))) ∨ ((p1 ∨ ((p4 ∨ p4) → False)) ∨ (True ∨ (p4 ∨ (p5 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640239855936836619254791129899 : (((((p2 ∧ (p2 ∧ p2)) → (((p2 → False) → False) ∧ (True ∧ (((p5 → (p1 ∨ False)) ∨ p1) ∧ (((p4 → p4) ∧ True) ∧ p2))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116648478140139885467889361654 : (((p3 → True) ∧ ((p2 → p2) → (((p4 ∨ (p1 ∨ ((False → ((True → False) ∨ (p5 → p1))) → (p4 → p4)))) → p1) ∨ p5))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116222450777922453989360408935 : ((((p4 ∨ p4) ∨ p4) ∨ ((p2 ∧ ((p3 ∧ (p3 → ((p4 → p2) ∨ ((((p4 → p1) → p2) ∧ p5) → p3)))) ∧ True)) → p4)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354008261650798114434150406403 : (p4 → (p3 → (p2 → ((((((False → (p4 ∨ (p4 → p2))) ∨ p5) ∨ p1) → p1) ∨ (p3 ∧ True)) ∨ (p2 → (p1 ∨ ((p3 ∧ p2) ∧ p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336164572664268703661622639092 : (p1 → ((((True ∧ ((p1 → (False → p3)) ∧ (p1 ∧ p3))) ∧ (((p3 ∨ ((p5 → (p3 ∧ p5)) ∨ (p3 ∧ p3))) ∨ False) ∧ p2)) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137778412518316865137095914961 : ((p2 ∨ (((((p1 ∨ p4) ∨ p5) ∨ False) → p5) → ((((p1 → True) → p1) ∨ p1) ∨ (((p4 ∧ p1) ∧ True) → p5)))) ∨ ((p2 → True) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (((p1 ∨ p4) ∨ p5) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_362228535163599141440282715143 : (((((p5 ∧ (((((True ∨ p4) → ((False ∧ p2) ∧ p5)) ∧ p4) ∨ ((p2 ∨ (False ∨ p1)) ∧ ((p5 → p2) → p1))) ∧ p2)) ∨ True) ∧ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46288764780018764956082792897 : ((((((p5 → ((p5 ∧ p4) → False)) ∨ False) ∧ ((p3 ∧ (p2 → p3)) ∨ ((False ∧ p5) → p1))) ∨ ((False ∨ False) → p1)) ∧ (p4 ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186859710065117921826742070680 : (((((True ∨ p2) ∧ p5) ∧ True) → (False ∨ ((p2 → p5) ∨ p5))) → (((p4 → (((True ∧ p2) → True) → (p3 ∨ (p1 ∧ True)))) → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354841815808383522953731610975 : (p5 → (((p4 → p1) ∧ (True ∧ (p3 ∧ ((p3 ∧ (p3 ∨ True)) ∧ (True ∧ (p3 ∨ ((((p2 ∧ (p2 → False)) ∧ p2) ∧ p2) → p3))))))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52101223522585109725918710183 : ((((p2 ∧ (p2 ∨ ((p4 → ((p1 → (p5 ∧ False)) ∧ (p5 → p4))) ∧ p1))) ∨ p4) → ((p5 → (p4 → (False ∨ (p2 ∧ p5)))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41410208441464011171253583278 : (((((((p5 ∨ (((p4 → False) ∨ p1) ∨ p3)) ∨ p3) → p1) → (p4 ∧ p1)) ∨ (((((p2 → p1) ∧ p3) ∨ True) → p1) ∧ p1)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50794766286365441549630714447 : (((True → ((p4 ∨ p2) → (p1 ∨ ((p5 ∧ (((((p3 ∧ p3) ∧ p5) ∧ p2) → p4) → p3)) ∧ p2)))) → (((p2 ∧ p3) → p1) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166187482003217804200395883046 : ((p1 ∧ ((p5 ∧ (p1 → (p3 ∨ ((p1 → ((p3 → (p4 ∧ p5)) ∨ p5)) → p1)))) → p3)) ∨ ((p2 → True) ∨ (((p5 ∧ p4) ∧ p2) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786565389424000272001869980551 : (((p4 ∨ ((((True → (p3 ∧ (p3 ∨ True))) ∧ (True ∧ True)) ∨ p5) → (p5 ∨ (((((p1 → p3) ∧ p5) ∧ p5) ∨ p3) ∧ (p2 ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38443088583364898274619735636 : ((((p2 ∧ (p2 → (((True → ((False → False) → p1)) ∧ p2) ∧ (p4 ∨ p5)))) ∨ (((p1 → p5) ∨ ((p3 → p4) → p3)) ∨ p5)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179307034513152296514008733640 : ((False ∨ (((p5 → (False ∨ False)) ∧ p1) → ((p2 → p5) → (p1 ∧ False)))) ∨ ((p1 ∨ ((p2 ∧ True) ∨ ((False ∧ True) → p4))) ∧ (True ∨ p4))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355884719267447033447653850705 : (p5 → ((p2 ∨ (((p4 ∧ (((p4 ∧ (((False ∧ (p3 ∧ (False → True))) → p2) → p5)) ∨ p2) ∧ p4)) ∨ p2) ∨ p2)) ∨ (p5 ∧ (p3 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57881594528362119340551536742 : (((p2 ∨ (p4 ∧ True)) → (((p5 → (False → False)) → ((((True ∧ ((False → p5) ∨ ((True ∧ False) ∨ False))) → p4) ∨ True) ∨ False)) ∨ p4)) ∨ False) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647923832589999471382391652501 : ((((((True → ((((True ∧ p2) ∧ ((p5 → p5) → (False ∧ p4))) → (p2 ∨ p4)) ∨ (p5 ∧ (p2 → False)))) → p5) ∧ p5) ∧ (False ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118557269164961103897905172831 : ((p3 ∨ (p4 → ((((p2 ∧ p4) ∨ ((p3 ∧ p4) ∨ p1)) ∧ (p2 ∧ (((p4 → p2) ∧ ((p1 → True) ∧ True)) ∨ p1))) ∧ False))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116321230385544639455436893799 : ((((p1 ∧ p5) ∧ p4) → ((((((p1 → (p2 ∧ (True ∨ True))) ∧ ((p2 ∧ (False → p2)) → p1)) ∨ p2) → True) ∧ p2) → p3)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619841550121859676205247919504 : (((((p3 ∨ p4) ∧ ((p3 ∨ ((False → (p3 → False)) → (p4 ∨ (((p1 → p4) → (p4 → p5)) ∧ (True ∨ True))))) ∧ (True → p5))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_136810380868963337710428003170 : (((p4 → p3) ∧ (((p4 ∧ ((p3 → p1) ∨ p3)) ∧ (p4 → (p2 ∨ (((p4 ∨ False) → (p1 → p2)) ∨ p1)))) ∧ p3)) ∨ ((p4 ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139843443659059197510792084270 : (((p3 → ((p1 ∧ (p2 → p5)) → ((((p2 ∨ (((True → p5) → p4) ∧ p2)) → p2) → p1) ∨ (p2 ∨ p4)))) → p2) → ((p3 ∨ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169011555602209053799638309769 : ((p1 → (p1 ∧ ((((p2 ∧ ((True ∧ (p3 ∨ p3)) → p5)) → (False ∨ p5)) → p1) ∧ p1))) → ((p5 ∧ (True → p3)) → ((p2 → p2) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158264202647993718855419240357 : (((p3 ∧ (p4 ∧ True)) ∨ ((((p3 → (False ∧ (p4 ∧ (p4 → p1)))) → p5) ∨ (True ∧ p5)) → p2)) ∨ ((p4 ∨ (p4 ∨ (True ∨ p2))) ∨ p5)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159270289177748421384543495879 : ((p4 → ((p3 ∧ (False ∧ (((True ∨ (((p4 → p4) ∧ True) → p3)) → False) ∧ (p2 → p4)))) ∨ True)) ∨ (((p4 ∧ p2) ∧ True) → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166221906523069839336822764781 : ((p2 ∧ ((((False → (p4 ∨ p5)) ∨ (True ∨ (p4 ∧ False))) → (p1 ∨ p4)) ∨ (False ∨ p5))) ∨ ((False → p3) ∨ ((False → False) ∧ (p1 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808766382266656475391860198110 : (((p4 → (p4 → ((p5 ∧ ((p2 → (False ∨ ((((p3 ∧ (True → True)) → p1) ∧ ((p5 ∧ (p1 → True)) ∨ p3)) → p1))) ∧ True)) ∨ p4))) ∨ p5) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327829462401646223225936567356 : (True → (((p4 ∧ (p4 ∧ ((False ∨ p3) ∨ ((((p5 ∧ ((p3 ∨ True) ∧ p5)) ∨ p3) → p5) ∧ (p5 ∨ p4))))) → (p4 → p2)) ∨ (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248261021760777058687334097361 : ((p2 ∨ p2) ∨ ((p5 ∨ ((p4 → ((((p2 ∨ (((p4 ∧ p2) ∧ p1) ∧ p5)) ∧ (p1 ∨ p5)) → (True → (p3 ∧ False))) → p1)) ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679744118054705711824669148247 : ((((((p3 ∨ ((p2 → p5) ∧ (p2 ∧ ((p5 → (False ∧ p3)) ∧ p1)))) → (p1 → (False → True))) ∨ p4) → ((True ∧ (p4 → False)) ∨ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119445518316770763756497772774 : ((p4 → ((p5 → (p3 ∨ (((p4 → True) ∧ (False ∨ p1)) ∨ False))) ∧ ((((p3 ∨ p3) → ((True ∧ p1) → p4)) ∧ p4) ∧ True))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172086690287469984282593563345 : ((((False ∨ p4) ∧ ((((p3 ∧ p2) → (False ∨ p4)) ∨ False) ∨ True)) → (p4 → False)) ∨ (p2 ∨ (((p2 ∧ True) ∧ (p5 ∨ (True → p3))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773590169913855271709691441293 : (((False ∨ (((p2 ∧ p5) ∨ ((p2 ∧ (((p1 → (p5 → (((True ∨ (p1 → (p2 ∨ True))) → False) ∨ p3))) ∨ p5) ∨ p2)) → p3)) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_780259651087155942636203181051 : (((p2 ∨ ((p2 ∧ (p3 ∨ (((p4 ∨ p2) → (p3 ∨ True)) ∧ ((True ∧ p5) ∧ (p2 ∨ ((p3 ∧ p4) → True)))))) → (p4 ∨ (p1 ∨ p2)))) ∨ p4) ∧ True) := by
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
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
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
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47376769884759481754496702903 : ((((p2 ∧ p2) → (((p4 ∨ (p1 → (p3 ∧ p5))) → p1) ∨ (False ∧ (False ∨ ((p5 ∨ p3) ∧ ((p4 ∧ p3) ∨ p2)))))) ∨ (p1 → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114038963926321603782395114588 : (((((((p3 ∧ ((((False → p2) ∨ p5) → p1) ∧ (p1 → p2))) ∨ p3) → True) → p4) ∧ (p4 ∨ p2)) ∨ (False → (p1 ∨ True))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117805461235759447624609996219 : ((p4 ∧ ((p3 ∨ (p4 ∨ p1)) ∧ ((((True ∧ (p2 → ((p4 ∨ p1) → p1))) ∨ p2) ∨ (p5 ∨ False)) ∨ (False ∨ (p2 ∧ True))))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136477296669453834148282680865 : ((((False ∧ False) ∨ True) ∧ ((p4 ∧ (p2 ∨ ((p4 ∨ True) ∨ (p2 ∨ (p2 ∧ ((p2 ∧ p4) → p1)))))) ∧ (p3 ∧ p1))) ∨ (p5 → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785050206806704477109548566265 : (((p4 ∨ ((((p5 → p4) ∨ ((((p4 ∨ p3) ∨ (((p2 ∧ (p4 ∧ ((p5 → p1) → p4))) ∨ p4) ∨ p2)) ∨ p4) ∨ p5)) ∧ True) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678405104237184464680572640797 : ((((((p3 ∧ (p5 ∧ p5)) → p4) ∧ (((True ∨ (p2 ∧ p2)) ∨ ((p3 ∧ False) ∨ p4)) ∧ (p3 ∨ False))) ∨ (((p1 ∨ p3) ∨ False) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693475255186543174199720638815 : (((((((False ∧ (((p3 ∨ p2) → p3) ∨ (True ∧ p1))) ∧ True) ∨ p4) ∧ p5) ∨ (((p2 ∧ p1) → (p3 → p3)) ∨ ((p2 ∧ p1) ∨ False))) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229422870647874944924834238285 : ((p1 → (True → p4)) ∨ ((p3 ∨ (((((p4 ∨ False) → ((p1 ∨ p5) ∧ p5)) → ((p5 → True) ∨ p1)) → p3) ∧ p5)) ∨ (False → (False ∧ p3)))) := by
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
theorem thm_5_vars_51772940520027363472915771160 : (((False ∧ (((p4 ∨ (p3 → p1)) → False) ∨ ((False → (p4 → (p5 ∧ p3))) ∧ p3))) ∧ (((p4 → (p1 ∨ (p5 → p5))) ∨ p2) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311305033883114589091727399733 : (p2 ∨ (True ∧ (True → (((((((p2 ∧ ((True ∨ (p3 → p4)) ∨ (p3 → False))) ∧ False) → True) → False) ∨ p4) ∧ ((p4 → p1) ∨ p1)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339011382588936395963614273230 : (p1 → (True ∧ ((p4 ∨ (p3 ∨ ((p5 ∨ p2) → (p2 ∨ ((p2 → (False ∧ True)) ∨ ((p1 ∧ True) ∧ (p4 ∧ p3))))))) ∨ ((p1 ∧ p3) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701622980576442212845148199356 : (((((p2 ∨ True) ∨ ((((p1 ∨ False) ∨ p3) ∧ p5) ∨ p2)) ∧ ((((p1 → True) → p5) ∧ p2) ∨ (False → ((p2 ∧ (p2 ∨ True)) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172140875696422894213286789469 : (((p4 ∧ ((p1 ∧ (p1 → (p4 ∨ (p1 → p4)))) ∨ p4)) ∧ ((p3 → p4) → p3)) ∨ (((p5 ∧ p3) → True) ∨ ((p2 ∧ (True → p2)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321475280640473117077058801426 : (p4 ∨ (p1 → (((((p3 ∨ (p5 → (p3 ∨ p1))) → p3) ∨ ((p3 ∨ True) → ((p1 → (p2 → True)) ∧ p3))) ∧ ((p2 → p5) ∨ p2)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66147424540133593423514227714 : ((p5 ∨ (((p3 ∨ ((p5 ∧ p1) ∨ ((p3 → p4) ∧ (((p2 ∧ (p1 → True)) ∨ (p4 ∧ (p5 ∨ True))) ∨ p3)))) ∧ True) → (p1 ∨ True))) ∨ p2) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318333611102855735048248271439 : (p4 ∨ ((p4 ∧ (((((p3 → p5) ∨ ((p2 ∨ (False ∨ ((p5 → (p5 → p1)) → p2))) ∨ (p5 → (p4 ∧ p4)))) → False) ∨ False) ∧ p4)) → p5)) := by
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
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : ((p3 → p5) ∨ ((p2 ∨ (False ∨ ((p5 → (p5 → p1)) → p2))) ∨ (p5 → (p4 ∧ p4)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h5
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h7
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40405734586413917658924518158 : ((((((((p2 ∧ p4) ∨ p2) ∧ ((((p4 ∨ (p5 ∧ p4)) ∧ True) ∨ p4) ∧ p5)) ∧ (p2 → True)) → (p1 ∨ (p5 ∧ p2))) ∨ p1) ∨ p2) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h5.left
    let h10 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h10
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h10
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h10
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h5.left
    let h21 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h21
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h21
        -- One of the premise coincides with the conclusion.
        exact h19
    case inr h29 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h21
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258786908241305542429421054148 : ((True → False) → ((p3 ∨ (((p5 → p1) ∧ (True ∧ (p5 ∨ p5))) ∨ (p5 ∧ p5))) → ((p4 → p4) ∧ ((p5 → (p3 ∧ p4)) ∧ (p2 ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h16
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h17 =>
    -- One of the premise coincides with the conclusion.
    exact h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h25 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h26 := h1 h25
        -- False on the left can always be used.
        apply False.elim h26
      case inr h27 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h28 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h29 := h1 h28
        -- False on the left can always be used.
        apply False.elim h29
    case inr h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h33 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h34 := h1 h33
      -- False on the left can always be used.
      apply False.elim h34
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h35 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h36 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h37 := h1 h36
    -- False on the left can always be used.
    apply False.elim h37
  case inr h38 =>
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h39 =>
      -- Conjunctions on the left can always be decomposed.
      let h40 := h39.left
      let h41 := h39.right
      -- Conjunctions on the left can always be decomposed.
      let h42 := h41.left
      let h43 := h41.right
      -- Disjunctions on the left can always be decomposed.
      cases h43
      case inl h44 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h45 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h46 := h1 h45
        -- False on the left can always be used.
        apply False.elim h46
      case inr h47 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h48 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h49 := h1 h48
        -- False on the left can always be used.
        apply False.elim h49
    case inr h50 =>
      -- Conjunctions on the left can always be decomposed.
      let h51 := h50.left
      let h52 := h50.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h53 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h54 := h1 h53
      -- False on the left can always be used.
      apply False.elim h54
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h55 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h56 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h57 := h1 h56
    -- False on the left can always be used.
    apply False.elim h57
  case inr h58 =>
    -- Disjunctions on the left can always be decomposed.
    cases h58
    case inl h59 =>
      -- Conjunctions on the left can always be decomposed.
      let h60 := h59.left
      let h61 := h59.right
      -- Conjunctions on the left can always be decomposed.
      let h62 := h61.left
      let h63 := h61.right
      -- Disjunctions on the left can always be decomposed.
      cases h63
      case inl h64 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h65 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h66 := h1 h65
        -- False on the left can always be used.
        apply False.elim h66
      case inr h67 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h68 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h69 := h1 h68
        -- False on the left can always be used.
        apply False.elim h69
    case inr h70 =>
      -- Conjunctions on the left can always be decomposed.
      let h71 := h70.left
      let h72 := h70.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h73 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h74 := h1 h73
      -- False on the left can always be used.
      apply False.elim h74
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h75 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h76 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h77 := h1 h76
    -- False on the left can always be used.
    apply False.elim h77
  case inr h78 =>
    -- Disjunctions on the left can always be decomposed.
    cases h78
    case inl h79 =>
      -- Conjunctions on the left can always be decomposed.
      let h80 := h79.left
      let h81 := h79.right
      -- Conjunctions on the left can always be decomposed.
      let h82 := h81.left
      let h83 := h81.right
      -- Disjunctions on the left can always be decomposed.
      cases h83
      case inl h84 =>
        -- We want to use the implication h80 based on <expert-advice>. So we show its premise.
        have h85 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h84
        -- We have shown the premise of h80, we can now drive its conclusion.
        let h86 := h80 h85
        -- One of the premise coincides with the conclusion.
        exact h86
      case inr h87 =>
        -- We want to use the implication h80 based on <expert-advice>. So we show its premise.
        have h88 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h87
        -- We have shown the premise of h80, we can now drive its conclusion.
        let h89 := h80 h88
        -- One of the premise coincides with the conclusion.
        exact h89
    case inr h90 =>
      -- Conjunctions on the left can always be decomposed.
      let h91 := h90.left
      let h92 := h90.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h93 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h94 := h1 h93
      -- False on the left can always be used.
      apply False.elim h94



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786010319049791693286589581764 : (((p4 ∨ ((p3 → ((p4 ∧ ((((p1 ∧ (p1 → p3)) ∧ p4) ∨ p2) → (((p5 ∨ (p5 ∨ p4)) ∨ p5) ∧ p3))) ∧ p2)) ∨ (True → True))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_225984338004648328305559526476 : (((p3 ∧ p4) ∨ False) ∨ (p4 ∨ (p3 → ((p4 ∨ True) ∨ (p2 ∨ ((p1 ∧ ((p3 → (p1 ∧ (((p2 ∧ p2) ∧ False) ∧ p4))) → p4)) ∧ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_589406194974811782596806622999 : ((((((((p2 ∧ (((False → p4) → p1) ∧ (p2 ∨ (p3 ∧ False)))) ∨ p3) → ((False ∨ (p5 → p2)) → (False → p5))) ∨ True) → p2) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40652339023730876296729536242 : ((((((p2 ∨ (((p4 → p1) ∧ p4) ∧ (p4 ∨ ((p5 ∨ p4) ∨ ((p4 ∧ p1) ∨ True))))) ∨ (p5 ∨ p4)) ∧ (p3 → p1)) → p4) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728148576708357084920023133722 : ((((p5 ∨ (p3 ∨ False)) ∨ ((((p4 ∨ ((p3 ∧ p4) ∧ True)) ∨ False) → p5) ∧ (((p2 ∧ (p4 ∨ True)) ∨ (p5 ∨ (True → p5))) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218523317140730598753032061265 : (((p4 ∨ True) → (False ∧ p4)) → ((p3 ∧ (((((p4 → True) → (p4 → ((False ∨ True) ∨ p4))) → (p5 ∨ True)) ∧ p3) → (p4 ∧ p5))) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (p4 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h5.left
  let h12 := h5.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h13 : (p4 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h13
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- False on the left can always be used.
  apply False.elim h15
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h16 : (p4 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h17 := h1 h16
  -- We need to get the left conjuct of h17 based on <expert-advice>.
  let h18 := h17.left
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113771614062644933277909410020 : ((((p4 ∧ ((False → p1) ∧ p3)) ∨ (p3 ∧ ((p2 → (p1 ∨ p5)) → ((True ∧ ((False → True) ∨ p5)) ∨ p5)))) → (True → p4)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776947697416182260095292485642 : (((p1 ∨ ((((p4 → ((((((p2 ∨ p4) ∨ (p1 ∧ (p4 ∨ p5))) ∨ True) ∧ False) ∨ False) ∧ (p3 → p3))) ∨ p1) → False) ∧ (p5 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118786137052151063388162034829 : ((p5 ∨ (True → (((((p5 ∨ ((False → True) ∧ p2)) ∧ p5) → (True → (p5 ∨ p5))) ∧ True) ∧ ((p2 ∧ p3) ∨ (p5 ∧ p4))))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619379895528645698605091090262 : ((((((p3 → False) → p4) → (((((p1 ∧ (p2 ∧ p3)) ∨ p3) ∧ (((p4 → p3) → True) → p5)) ∨ (True ∧ p3)) ∧ (True ∧ p1))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



