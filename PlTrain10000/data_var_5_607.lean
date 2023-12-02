variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56792647184140086952173240096 : ((((True ∨ p1) → True) ∧ (p5 → (True → ((((p2 ∧ ((((p4 ∧ p4) → False) ∧ True) → p2)) ∧ ((p4 ∧ p5) ∧ True)) ∨ p5) ∨ True)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165282455991746325741032090145 : (((((p2 ∧ ((True → p3) → (p5 → False))) → p4) ∧ ((True ∨ p1) ∨ p2)) → (True → p1)) ∨ (p3 ∨ (((p4 ∧ (p5 → p1)) → p4) ∨ p4))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126149343980684785758840545418 : ((True ∧ ((p5 → p4) ∧ (p1 ∧ (((((((p4 ∨ p5) → p2) → ((p2 ∧ (True ∧ p5)) ∧ p5)) → p1) ∧ p3) → p4) ∧ True)))) → (p4 ∨ p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199451723338062681180850711474 : (((p3 ∧ (p5 → (p2 → (p3 → p3)))) ∨ p4) → (((((p3 ∧ True) ∧ (p4 ∨ False)) → (p4 → p4)) → ((True → False) → (False ∨ p4))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314068661387160308227583124998 : (p3 ∨ (((p5 ∨ (p2 → ((p1 ∨ (True ∧ ((p2 ∨ p2) ∨ p1))) ∨ ((p3 ∨ (((p1 → p1) ∨ p2) ∧ p3)) ∧ p5)))) → p1) → (p1 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ (p2 → ((p1 ∨ (True ∧ ((p2 ∨ p2) ∨ p1))) ∨ ((p3 ∨ (((p1 → p1) ∨ p2) ∧ p3)) ∧ p5)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762310749469810090347247490082 : (((p3 ∧ ((((p5 ∧ p2) ∨ p1) ∨ (True → (False → (((p2 ∨ (True ∨ p4)) ∧ (p5 ∧ (p4 ∨ p3))) → p1)))) ∧ ((True ∧ True) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69036592063238358298882497986 : ((p5 → ((((False ∧ (False → p4)) ∨ (p2 ∨ ((False → ((False ∨ True) ∧ (False ∨ (True → p5)))) → False))) ∨ ((p4 ∧ p3) ∧ p2)) ∨ p5)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178398917454676521662371935282 : ((((p1 ∧ (p2 ∨ p4)) ∨ (((p1 ∧ True) ∨ p1) → p4)) → (p2 ∨ p1)) ∨ ((p1 ∧ ((True ∧ ((p3 ∨ False) ∨ (False → p3))) ∨ p1)) → p1)) := by
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
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40611501850791161984343201195 : ((((((p1 ∨ ((p3 ∨ (p5 → (p1 ∨ p5))) ∧ True)) ∧ ((True ∨ (p3 → False)) → ((p2 ∨ (p4 → p2)) → False))) ∨ p4) → p2) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756338202130985502742502429935 : (((p1 ∧ ((((True ∧ (True → ((p5 → False) ∨ (p4 ∨ (((False ∧ (p3 ∧ p5)) ∧ False) ∧ p2))))) → p1) ∨ True) ∧ ((p3 ∨ p3) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38851650957486532342920482061 : (((((p4 ∨ p2) → True) ∧ ((((((p4 ∧ (p5 ∨ (p5 ∨ p3))) ∨ True) → False) ∨ False) ∧ (p3 → (p1 ∧ True))) ∨ (p3 → p4))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657431215277867689582825266715 : (((((False ∧ False) ∨ (((p3 ∧ (((p1 → False) ∨ ((((p4 → False) ∨ True) ∧ (p4 ∨ p2)) ∧ True)) → p5)) → p4) ∨ p4)) ∨ (p2 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119574504451721426584026252304 : ((p5 → (((True ∧ (p1 ∧ False)) → True) → ((((True ∨ (((p3 ∧ p1) ∨ p3) ∨ (p4 → p2))) → p3) ∧ p3) ∨ (p3 → True)))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37680276290745899179752492788 : (((((p1 ∨ (((True ∨ p5) ∧ p4) ∨ ((((p2 → p4) ∧ ((p5 ∧ (p3 ∧ p1)) ∨ True)) → True) → p1))) ∧ (p4 ∨ True)) → False) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_583249139337597134212863857 : ((((p5 ∨ ((True ∧ p4) ∨ (p4 → (True → ((p4 → (p1 ∧ p3)) ∨ p1))))) ∨ ((p2 → p4) ∧ (p2 → (p1 ∧ False)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56220540550232135763963535769 : (((p2 ∨ (p2 ∨ (True ∧ p3))) ∨ (((p3 ∧ (p4 ∨ ((False → True) → (((True → (p4 ∧ p4)) ∧ (False → p1)) ∨ False)))) → p1) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46972530035538322738208576716 : (((((((False → (True → (False ∨ p4))) ∨ True) → (p2 ∧ (False ∨ (True ∧ ((p1 → (p1 ∧ p4)) ∨ p4))))) → False) → False) ∨ (p3 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689932018794968398731441805149 : ((((True ∧ (((p4 → p1) ∧ ((((p5 ∨ p3) ∧ p3) → (p4 ∧ p4)) → p3)) ∧ p2)) ∨ (True → (((p2 → p2) ∧ p1) ∧ (p3 → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646668696156395121172925365950 : ((((p1 → (p4 → ((p3 ∨ p4) ∧ ((((p2 → False) ∧ (p4 → p1)) → (p3 ∧ ((p2 → (False → p3)) → (p5 ∨ True)))) → True)))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160248948329088956719549882357 : ((((p5 ∧ True) ∨ (((p2 ∧ p5) → (p1 → p2)) → (((p2 ∧ p3) ∨ p4) ∨ p4))) ∨ (p3 ∧ True)) → (p4 ∨ (((p1 → p1) → p5) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : (p1 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h11 := h8 h9
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h18 := h15 h16
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184741381303194464478126034071 : ((((p2 ∨ (True → False)) ∨ p1) ∧ (((p2 → p3) ∧ True) ∧ False)) ∨ (p4 ∨ ((True → (True ∨ True)) ∨ (p3 ∧ (False → ((p4 → False) ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61038330025798815633586285776 : ((False ∧ (((True ∧ ((p2 ∧ ((p2 ∧ ((p5 → p5) ∧ p3)) ∧ (p2 ∧ p4))) ∧ (True → p5))) ∧ (True ∨ (p2 ∧ True))) ∨ (True → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_460710318535974997934166839319 : (((((((p4 ∧ ((p5 ∧ p4) ∧ (p2 ∨ p3))) ∧ ((p4 ∧ p3) → p5)) ∨ True) ∧ True) ∧ (True ∨ (p3 ∧ ((True ∨ (False → p2)) ∨ p4)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666760496804120211811833699464 : ((((((p5 ∨ (p4 → (p1 ∧ (False ∨ True)))) ∨ p5) ∧ (((p5 ∨ (True ∨ (p5 ∧ (p4 ∧ p2)))) ∧ False) ∨ p2)) ∧ ((True ∧ p2) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192916283973378014486722335951 : (((((p4 ∧ (p5 → p4)) ∨ p1) ∨ p3) ∨ (p2 → True)) → (p1 → ((((p1 → (False → p5)) → (False ∨ p1)) → (p1 ∧ False)) ∨ (False → p4)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
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
theorem thm_5_vars_69205244950579447154352869584 : ((p5 → ((((p4 ∧ p5) ∧ True) ∨ ((p3 ∧ p3) ∧ p1)) ∧ ((p5 ∧ ((p1 → (False ∨ (p2 → (p2 ∨ p3)))) → (p1 → False))) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248576767619520615970700994001 : ((p3 ∨ False) ∨ ((((p4 → ((p2 ∨ p3) ∧ p2)) → (p4 → ((p4 ∨ (p5 → (True ∧ p1))) → p4))) ∧ (p5 ∨ p5)) ∨ (p5 → (p4 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175416503849257998278516615554 : ((False → ((p4 ∨ p1) ∨ ((p4 ∧ ((p4 ∨ (p1 → p3)) ∧ (True → p5))) ∨ True))) → ((p2 ∧ (p4 ∧ (((p1 ∨ p2) ∨ p3) → p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51745493658576076250906575365 : (((((p4 ∧ p4) → False) → (((False ∨ p3) ∨ (p1 ∧ (p1 ∧ p4))) ∨ (p4 → p2))) ∧ ((p3 ∧ p1) ∧ ((p3 → (True ∨ p3)) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50366949373017265186596041442 : (((((p4 ∨ p1) → p4) ∨ (False ∧ (((False → p1) ∨ p3) ∧ (p4 ∧ (((p1 ∨ p4) ∨ p5) ∧ p3))))) ∨ ((False ∧ p5) → (p2 ∨ True))) ∨ False) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56233063846959134676344308333 : (((p4 ∨ (p2 ∨ (p1 ∨ p3))) ∨ (p3 ∨ ((p5 → True) ∨ ((False → p5) ∧ (p3 ∧ (((True → p1) → ((True ∨ p3) ∨ p2)) → p3)))))) ∨ p2) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672524580404143416811792620333 : (((((p4 → ((((p5 ∧ p5) ∨ False) ∧ p2) ∨ (((False ∧ p4) ∨ p3) → (p3 ∨ (False ∧ (p2 ∧ p1)))))) → True) → ((p3 ∧ True) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47238280686716576447338479061 : (((((p5 ∨ (p4 → ((False ∧ p1) ∨ False))) → p3) → (p4 ∧ ((True → ((p5 → (False → p5)) ∧ (p1 ∧ p5))) → p3))) ∨ (p1 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18845467136147836829998866156 : (((((((p5 → False) ∨ (p2 → p5)) ∧ p5) → False) ∧ (((p3 ∨ p5) → p3) → (p4 → p3))) ∨ ((p4 ∨ (p1 ∧ p3)) ∨ (p2 → True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_185577863342545906426916564226 : ((p5 ∨ ((p1 ∧ (p2 → ((p3 → (p1 ∨ p5)) → p3))) ∧ p1)) ∨ (False → ((True → (p2 ∨ (((p3 ∧ p3) ∧ True) ∧ (p5 → p2)))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197738648734585455317125273914 : ((((p5 ∧ True) → False) ∧ ((p3 ∧ False) ∨ p1)) ∨ ((p4 → p2) → (((True → ((True ∧ (p5 ∧ p4)) → ((p5 ∧ p1) ∨ True))) ∨ p1) ∨ False))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155513770848968387999221049027 : (((False ∧ (p2 ∧ p3)) ∨ (p4 ∨ (True ∨ ((False ∧ ((p4 ∧ p3) → (p1 ∨ p1))) → (p1 → p2))))) ∧ (((False → False) ∧ p2) ∨ (p5 ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756681430708277740727017965904 : (((p1 ∧ (((p3 ∧ (False ∧ (((p4 ∨ p4) ∨ p2) ∨ (p4 ∨ (False ∨ p3))))) ∨ p5) → (p4 ∧ ((p4 ∧ ((p4 → p3) ∨ p4)) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266024364661912860791664583373 : (True ∧ (p1 → (((p5 ∨ p3) → ((p1 ∨ False) → True)) ∧ ((((p4 ∨ (((p4 ∨ p1) ∧ True) → ((p4 → p5) ∧ p5))) ∨ p1) ∨ p4) ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_66056498308033458049887566133 : ((p5 ∨ (((False → ((p1 ∨ (p2 → ((p2 → (True → (False → p3))) → (p3 ∨ p2)))) ∨ ((p1 → (p4 → p1)) ∨ p3))) → p5) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702882623284733113899673136679 : ((((((p4 → (p5 → p3)) → p4) → (p4 ∧ (p2 → True))) ∨ ((p2 ∧ (p2 → ((p3 → (True → False)) ∧ p4))) ∨ (True ∨ (True ∧ p3)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688817548784494747451676035375 : (((((((True → True) ∧ ((False ∧ (((p5 → p5) ∨ p1) ∨ p3)) ∨ False)) ∧ True) ∧ p4) ∨ ((p5 ∧ (((p5 ∧ True) → True) ∨ False)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668850732225726044818968107047 : (((((((p2 ∨ (True ∧ p1)) ∧ p3) ∨ ((p1 ∨ (p2 ∧ True)) ∧ ((p4 ∨ ((True ∨ True) ∨ True)) → p2))) ∨ p5) ∨ ((p3 ∨ p2) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58697288663143136145910014804 : (((p2 → p3) ∧ (p3 → ((p3 → True) → (p3 → (p5 ∨ (((p1 ∨ (True ∧ p4)) ∨ (p1 → p3)) → ((p2 → p5) ∨ (p5 → True)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148911114570332338743342472618 : (((((True ∨ False) → p3) ∧ p5) → ((p3 ∧ ((p5 → (p5 → ((True ∨ p5) ∧ p2))) ∨ False)) ∨ (p5 ∧ p1))) ∨ (((p3 → True) ∨ p4) ∨ p3)) := by
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
theorem thm_5_vars_204179718883743983575230721040 : ((((p4 ∨ (p4 ∧ p5)) ∨ False) ∧ p1) ∨ (((False ∧ p5) → (p2 ∧ (p1 ∧ ((p5 ∨ ((p4 ∨ False) → (p1 → (False ∨ p3)))) ∨ p1)))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313336737694052317251529448795 : (p3 ∨ ((True → (((((((p5 ∨ p5) → p5) ∨ p5) ∧ (p1 ∨ p1)) ∨ (p3 → (False → (p4 ∧ p2)))) → (p4 → (p4 ∨ p3))) ∨ p3)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326170139045996708894589929940 : (p5 ∨ (p2 → ((((False → (p1 → (((p3 ∧ ((p4 ∨ p4) ∧ ((False ∧ (True → p4)) → False))) → p1) ∧ False))) ∨ False) → p1) ∨ (True ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244092269805741884216728031438 : ((True ∧ p3) ∨ (((p4 ∨ ((p2 ∨ p2) → (p2 → p2))) → p2) ∨ ((p1 → ((p3 → p2) ∨ True)) ∨ (((True → p5) → p4) ∧ (p2 ∧ p3))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355828787445575769406395175195 : (p5 → ((((p2 ∨ (((((p2 ∧ p4) ∧ p1) ∧ (True → (p4 → (p5 ∧ p3)))) ∧ p2) → (p3 → False))) ∧ p3) ∧ p5) ∨ ((p5 ∨ True) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_389532254159475437851261664159 : (((((False ∨ ((p3 → (p3 → p3)) ∧ (p3 → ((p4 ∨ (False → p3)) ∨ p3)))) → (((p5 → p5) ∧ ((p1 → p4) ∧ True)) → p3)) ∨ True) ∧ True) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180178158936364880698971204665 : ((((p3 → (True → ((p4 ∧ p1) → p5))) → ((True ∧ p5) ∨ p3)) → p2) → ((p1 ∨ (True → p5)) ∨ ((p3 ∧ p1) → (p3 ∨ (p1 → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602798405342688936599242734199 : ((((False ∨ (p3 → ((p1 ∧ (((p5 ∧ (p4 ∨ p4)) ∧ (False ∧ (p1 → ((((False → p3) ∨ False) ∨ False) ∨ p2)))) ∨ True)) ∨ True))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204500585421863308817875000078 : ((((p5 ∧ (p5 ∧ p5)) ∨ p1) ∨ p1) ∨ (((p4 ∧ (p3 ∧ p3)) ∧ (p4 → (p2 ∧ ((p2 ∨ p5) ∨ p4)))) ∨ (((p5 → p1) → p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67830003125342030595180783438 : ((p2 → (((p3 ∨ (False ∧ ((True → ((True ∧ p2) → (p3 ∧ p4))) ∧ p3))) ∨ (((p2 ∧ False) ∨ (p1 ∨ True)) ∨ p1)) ∧ (p3 → True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165667749080003940147539804851 : (((p2 ∨ (((False → p3) ∧ p1) ∧ False)) ∨ (((False → p4) ∨ (p5 ∧ p1)) → (p1 ∧ p1))) ∨ ((True ∨ (p1 ∧ p3)) ∧ ((False ∧ p5) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175922474488536342999832260131 : ((((p3 → False) → (((((p3 → p5) ∧ p5) ∨ True) ∨ p4) → p3)) ∨ True) ∧ (((True ∧ (p1 → p1)) ∨ p2) ∨ (True → ((p3 → p1) ∧ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51732141009823613680183647875 : ((((p1 → ((p4 ∧ p3) ∨ p1)) ∨ (p3 ∨ ((((p1 ∧ True) → p3) → False) ∧ p2))) ∧ ((p5 ∨ ((p1 ∨ False) → p3)) ∧ (p4 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197593746351768655843298671512 : (((False ∨ ((p3 ∨ p5) ∧ p4)) ∨ (p1 ∨ True)) ∨ (((p2 ∨ p1) → (False → ((False ∧ ((p1 ∨ True) ∧ p1)) ∨ p4))) → ((p1 → False) → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178598098068822599551393932160 : ((((True → (False ∨ p4)) → (False ∧ p2)) ∨ (p4 → (p3 ∨ (p5 ∧ True)))) ∨ ((True ∧ False) ∨ ((p4 ∧ (p3 ∧ p3)) → (p2 → (p1 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328342054577050964915434602976 : (True → ((((p3 → p4) ∧ (p3 ∧ True)) ∨ (p2 ∨ ((p2 ∨ False) ∧ ((p1 ∧ (False → False)) → (p2 ∧ p2))))) → (((p2 ∨ False) ∧ False) ∨ True))) := by
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
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171651117630963531268070729251 : (((True ∧ ((True ∧ p1) ∧ ((p2 → False) ∨ (((p1 ∧ p4) ∨ False) ∧ True)))) ∨ p5) ∨ ((p2 ∨ (p1 → ((True → (p4 → p1)) ∧ p1))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47190388173743118848183921442 : (((((((True ∨ p2) ∨ p3) ∨ (p1 → ((p3 ∨ p2) → p5))) ∧ False) ∨ ((p5 → p1) ∨ (p5 → ((False → p4) → False)))) ∨ (p5 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649325247483319439326273088025 : (((((p3 ∨ ((True → ((p5 ∧ (((((p1 → False) ∧ p4) ∨ p4) ∨ p4) ∨ (p3 ∧ (p4 ∧ p5)))) ∧ p2)) → p4)) → p5) ∧ (True ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187541073408605996144353312265 : ((p2 ∨ ((((p2 ∨ p1) ∧ (p3 → False)) → (p3 ∨ p4)) → p1)) → (((p1 ∧ (p5 ∨ p4)) ∧ (((p5 → p5) ∨ False) → False)) → (p4 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h11 : ((p5 → p5) ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h13 := h5 h11
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h17 : ((p5 → p5) ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h18
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h19 := h5 h17
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115448066130527457253647122150 : (((((False ∧ p4) ∨ p4) ∨ (p4 → (p5 ∨ p3))) ∨ ((True → (True ∧ False)) ∧ ((p4 → (p4 ∧ True)) ∧ ((p2 ∨ p2) ∧ p2)))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611150447751061403471514422369 : ((((((p5 → (p1 → p1)) ∧ (p2 ∧ ((False → ((p2 ∧ (True ∧ (p4 ∨ (False → (p5 → p2))))) → (False → p2))) ∨ False))) → p5) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_808823972568715669870843667394 : (((p4 → (p5 → (((False ∧ p4) → p4) → (p1 ∨ ((p5 → p1) ∨ (False ∨ (p3 → (((p1 ∨ True) ∧ p5) ∨ (p2 ∨ (p3 ∧ p1)))))))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303777891680618563464552038542 : (p1 ∨ (((p3 ∨ ((((True → (True ∧ (p5 ∧ p4))) ∨ False) ∧ (p5 ∧ True)) ∨ ((p2 ∧ p3) ∨ (p3 ∨ (True ∨ (p5 ∨ p4)))))) ∨ False) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792868335246816656534768431307 : (((True → (((False ∨ p3) ∨ p3) → (((((p3 ∨ ((p5 → (p4 ∧ p3)) → p3)) ∧ (p1 ∧ p5)) ∨ False) ∨ (p2 → p3)) ∨ (p1 ∧ p4)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185285139554054387247366537907 : ((p2 ∧ (((((p5 ∧ p5) ∨ p2) → True) ∧ True) ∧ (p3 → True))) ∨ (((((p4 → (p4 ∨ p2)) → (p1 → p1)) → p4) → p5) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186522950551830662216897584466 : (((((p4 → (p1 → p3)) ∧ (p2 → p4)) ∨ p4) ∨ (p3 ∧ p5)) → (((p4 → p4) ∧ (False ∧ p4)) ∨ ((False ∧ ((True → p5) ∨ p1)) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
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
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113858964635577448503133260191 : (((p2 → ((True ∨ (((p2 ∨ p4) ∧ (p5 ∧ False)) ∨ (False → False))) ∧ (((True ∨ p1) ∧ p4) ∧ (False ∧ True)))) → (p2 → p1)) ∨ (p3 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135622569345943851217264268582 : (((p4 → ((False → p4) → (((p5 → ((p1 → p1) ∨ (p2 ∧ True))) → p3) ∧ False))) ∨ (True ∨ ((p3 ∧ p2) ∧ True))) ∨ (True ∧ (False ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62423226307103907412074558385 : ((p3 ∧ ((((p4 → p5) → p4) ∨ p5) ∧ (p5 ∧ ((p1 ∧ (((p2 ∨ p3) ∨ False) → ((True ∧ (p1 ∧ (p3 ∧ p3))) ∧ p5))) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803674624760658811714627807825 : (((p3 → ((p2 ∨ ((((p3 ∧ ((p4 ∨ p5) ∨ ((True ∧ (p3 ∨ p4)) ∧ p3))) ∨ (p5 ∨ False)) ∧ p5) → ((p1 ∨ p5) ∨ False))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107813587271566763940729306433 : (((p4 ∧ p2) ∨ (((p5 ∨ ((p5 ∧ (False ∧ False)) ∨ (((p1 ∧ (True → p3)) → p5) → False))) ∨ True) ∨ ((p1 → True) → p5))) ∧ (False → p5)) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324074065422612779393479864550 : (p5 ∨ (((p4 → (((False ∧ p1) ∨ (False ∨ True)) ∧ (p5 ∧ p2))) ∨ p5) ∨ (True ∨ (False ∧ (((((False → p1) ∧ False) ∧ p1) ∧ p3) → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177432674197676775829189379199 : ((True → (((False ∨ p1) ∨ ((p2 ∧ p3) ∧ p3)) ∨ ((p1 ∨ p2) ∨ True))) ∧ (p1 → (p1 ∨ (((p1 ∨ True) ∨ (p1 ∧ False)) ∨ (p5 ∧ p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65655895594687332275481735406 : ((p4 ∨ ((p5 ∨ ((p4 ∧ ((p4 ∨ (p5 → (p3 → ((False → (p2 ∨ (False ∨ (p1 ∨ p1)))) → (True ∧ False))))) ∨ True)) ∨ p4)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50674193890712301109542422227 : ((((p1 → (((p1 ∨ p2) ∨ p5) → p4)) → (True ∧ ((p1 ∧ True) ∧ (p2 → (p4 → (False ∨ p4)))))) → (((p5 ∧ p2) ∧ True) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711217026613909880716127812112 : ((((p4 ∧ ((False ∧ (p5 ∧ p5)) ∧ p3)) ∧ ((p1 ∨ (p5 ∨ ((p2 → True) ∧ (p3 ∧ (p2 ∨ p3))))) → ((p1 ∨ (False ∨ p3)) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305709806853166563172386629901 : (p1 ∨ ((((True → p2) → True) ∧ (((True ∨ p3) ∨ p1) ∨ True)) → (((True ∧ p3) → ((p4 ∧ p4) ∨ True)) ∨ ((False → False) → (p3 ∧ p3))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h15
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h18 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h19
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47267744397638979198208607431 : ((((((p3 ∧ True) ∨ p5) → p5) ∧ ((p4 → p2) ∨ (p2 → (p5 ∨ ((p3 ∧ (((p1 → p4) → False) ∨ p3)) ∧ p1))))) ∨ (False → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257500290069418578837936552766 : ((p3 ∨ False) → (((p2 ∨ ((((p4 ∧ p2) ∧ False) ∨ (((((p5 ∧ True) → False) ∨ p3) ∨ p2) ∧ p2)) ∨ p2)) → (p2 ∧ p4)) ∨ (p4 → p4))) := by
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308536660647667966929379122305 : (p2 ∨ (((p3 → (True ∧ ((((True ∨ p5) ∧ (p5 ∨ p4)) ∧ p3) → False))) ∨ ((((p2 → p2) ∧ p3) → p2) ∨ (p5 ∨ (False → p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120533633362648591179975330075 : (((((p1 → (((((False → (False → (p5 ∨ ((p1 → p1) ∨ (p5 → p2))))) ∧ p3) → p5) → True) ∧ p3)) ∧ p4) ∨ p2) ∨ False) → (p2 → p2)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251125077090499169247766501936 : ((p2 → False) ∨ ((((p2 ∧ p5) ∨ (p5 → ((((False ∧ ((p3 → p1) → True)) ∨ True) → ((p1 → p4) ∨ p2)) ∧ True))) → False) → (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201092986813209671800182567934 : ((True → ((((p2 ∨ True) → p3) ∧ p2) ∧ p5)) → (((True ∧ ((p4 → p4) ∧ (False ∨ ((True → (False ∧ p3)) ∨ p1)))) ∧ (True ∨ p4)) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h12 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h13 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h14 := h1 h13
        -- We need to get the right conjuct of h14 based on <expert-advice>.
        let h15 := h14.right
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h17 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h18 := h1 h17
        -- We need to get the right conjuct of h18 based on <expert-advice>.
        let h19 := h18.right
        -- One of the premise coincides with the conclusion.
        exact h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h21 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h22 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h23 := h1 h22
        -- We need to get the right conjuct of h23 based on <expert-advice>.
        let h24 := h23.right
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h25 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h26 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h27 := h1 h26
        -- We need to get the right conjuct of h27 based on <expert-advice>.
        let h28 := h27.right
        -- One of the premise coincides with the conclusion.
        exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2665050643252596472573485870 : (((p4 ∨ p5) → ((p2 ∨ False) ∧ p3)) ∨ ((True ∧ ((p3 → p2) ∨ ((p1 ∧ (((False → True) → (p1 ∨ False)) ∨ p5)) ∨ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685141377888632003915019511137 : ((((p3 ∨ ((((p3 ∨ p1) ∨ True) ∧ (False ∧ ((True → (p3 → p5)) ∨ True))) ∧ (p3 → True))) ∨ (p2 → ((p1 → (p4 → True)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65967019490751203576106522806 : ((p4 ∨ (p5 ∨ (p5 → (p4 ∨ ((((((p2 → ((p4 → p2) ∨ p1)) ∧ True) ∨ p3) ∧ p4) ∨ (p4 ∧ (p1 → p3))) ∨ (p5 → p5)))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151243791727196864492284854600 : ((((p2 ∧ p3) ∨ ((((False ∧ (False ∧ (False → (True ∧ (p2 ∨ False))))) → p4) → p5) → (True ∧ p2))) → p5) → (p4 ∨ (p4 → (p2 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114566458776537571419110308903 : (((((p5 ∧ p2) ∨ ((True ∧ ((False ∧ p2) → (p1 → p1))) ∧ True)) ∧ (p1 ∧ False)) ∧ (((p1 ∨ p4) → p4) → (p4 ∨ p2))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114732883320160119802182741507 : ((((((p3 ∧ (p3 ∧ True)) ∨ p4) → p3) → (((p4 ∧ p5) ∨ (p4 → p4)) → p1)) → (p1 ∧ ((p2 ∧ True) ∧ (p5 → p1)))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188675687039633743170130100247 : (((p3 ∧ (p5 ∨ ((p5 → True) ∧ p3))) ∨ (False → False)) ∧ ((((True ∧ (p2 → ((p2 ∧ p2) ∨ (p5 → p5)))) ∧ (p5 → p3)) ∧ p1) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149868203679068121936825524765 : ((p2 ∨ ((((((False ∧ p4) → True) ∧ False) ∨ (p4 → (((p3 ∧ p5) → False) ∧ (True → p1)))) ∨ p2) → False)) ∨ (True ∨ (p5 ∨ (p4 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70901619675652628295866820323 : (((((False → ((False ∧ p1) ∨ (False → (p1 ∧ p4)))) → p5) ∧ (((p3 ∨ (((p1 ∧ (p3 ∧ p3)) → p3) ∧ p1)) ∨ p1) → p2)) ∧ True) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (False → ((False ∧ p1) ∨ (False → (p1 ∧ p4)))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705248501390234648977099398478 : (((((False ∨ (((p5 ∧ p3) → p1) ∨ p2)) ∧ p5) ∧ (((((p4 → True) ∧ p5) ∧ (p3 ∧ (p5 ∧ p4))) ∨ p4) ∨ ((False ∨ p2) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149679875064187436014606738234 : ((p5 ∧ ((False ∨ ((p1 ∨ ((((((p5 ∧ p3) ∨ p1) ∧ p5) → False) ∧ p3) ∧ (p1 → p2))) ∨ p1)) ∨ p2)) ∨ ((p4 ∧ (p1 → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



