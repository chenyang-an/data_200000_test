variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112724739377264992684942567514 : ((((p1 → (p4 ∨ (p1 → ((((p3 ∨ True) → p4) ∧ False) ∧ (p2 → p2))))) ∨ ((p3 → (p5 ∧ (True → False))) → p2)) → p3) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698746047900217760846368763938 : (((((p5 ∧ p2) ∨ ((p1 → ((True ∧ p2) ∨ (p4 ∨ True))) ∧ False)) ∨ (False → (p5 ∧ (p1 ∨ ((p4 ∨ p1) → ((False → p5) ∨ p5)))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657989650805691023966933853808 : ((((p2 ∧ ((p4 ∧ (((p5 ∧ p5) ∧ p3) ∧ (((((p3 ∧ p2) ∨ p5) → p1) ∨ False) ∧ p3))) ∨ ((p3 ∧ p2) ∧ p1))) ∨ (True ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159064148856772782128519686962 : ((p5 ∨ ((False ∧ p2) ∨ ((p4 ∧ ((((p4 → p2) ∧ p4) ∨ (True → p5)) ∨ True)) ∧ (p2 ∧ p5)))) ∨ ((p1 ∨ True) ∨ ((False ∧ p1) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615016940618465659227842359597 : ((((((p2 ∧ p3) ∨ (((((p5 → p1) → p5) → False) ∧ True) ∨ (p3 ∨ ((p2 ∧ p2) ∨ p4)))) → (((p5 ∧ True) ∧ p3) ∨ p5)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_117079429194334116702671289570 : (((False → False) → ((((p5 → (True → ((True ∧ p2) ∧ (False → (True ∧ False))))) ∨ p4) → False) ∨ (((p1 → True) ∨ p1) ∨ False))) ∨ (p3 ∧ p3)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84670336109998341569221533737 : ((((p1 → ((p3 → p5) ∨ (p2 ∧ (p1 → ((p3 ∧ False) → p3))))) ∧ p5) ∧ (p5 ∧ (((p3 ∨ True) → p3) ∨ ((p2 → p1) → p5)))) → p5) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234632923341136639205369673648 : ((p3 → (p2 → p1)) → ((p5 ∨ (((p1 ∧ p1) ∨ (((p1 ∧ p2) ∧ True) → p1)) ∨ ((p1 ∧ True) ∧ ((p1 → (p2 → p3)) ∧ p4)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264830442755858868591614036980 : (True ∧ ((False ∨ p1) ∨ (False ∨ ((((p2 ∨ (p4 ∨ p4)) ∧ (True → False)) ∧ p5) → (p3 ∨ ((p4 → True) ∨ ((p3 ∧ (p4 ∧ p2)) ∧ False))))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h12 := h5 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h15 := h5 h14
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157091403210676801647821075546 : (((True → (((p1 → p2) → (p1 ∧ p5)) ∧ (((p2 ∨ False) → (p1 ∧ p4)) → (p3 ∨ p2)))) ∨ p2) ∨ (p2 ∨ (((p3 ∨ p3) → p3) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42394641495275157325482407064 : (((p4 ∧ ((True → p5) ∨ (((True → ((p1 ∨ (p2 ∧ (p1 ∧ False))) → (((False ∨ (p2 ∧ False)) ∧ p2) ∧ p4))) ∧ p5) → p4))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42224329216416701010717490390 : (((False ∧ ((p5 → (False → (p3 ∨ ((False → p1) ∧ ((p5 → p3) ∨ ((p2 ∧ (False ∨ (p3 ∨ False))) ∧ p2)))))) → (p4 → p2))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1971761880476578302470775382 : ((p2 ∧ ((((p2 → p2) → True) ∧ ((((True → False) ∨ p4) ∧ p1) → False)) ∨ ((p2 ∨ p3) → p1))) ∨ ((p1 ∨ True) ∧ (False → True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118291810351594034029250240351 : ((p1 ∨ (True ∧ (((p3 → (p2 ∨ ((False ∨ (False ∨ p1)) ∨ (False → p4)))) → p4) ∧ (p5 ∨ (p3 ∧ ((p4 → False) ∨ p4)))))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207376103059152582758146636137 : (((True ∧ (p5 ∧ (p3 ∨ p4))) ∨ p4) → ((p4 → ((False ∨ p2) ∨ (False → p4))) ∨ (((False → (p2 → (p1 ∧ (p1 → p5)))) → True) → p3))) := by
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
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h13
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704890039735885141727629732160 : ((((p3 ∨ ((((p2 ∧ (False ∨ True)) ∧ p2) ∧ True) ∨ p3)) → ((p4 → False) → (True → (((p2 ∨ p5) ∨ (False ∨ p5)) ∨ (p2 ∨ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768143420374475805077608801898 : (((p5 ∧ ((p5 ∧ (((p4 ∨ p4) ∨ ((True → ((p5 ∨ (p1 ∧ ((p5 ∧ False) ∧ (p3 ∧ p4)))) → p2)) → p2)) ∨ p5)) ∨ (p5 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164780675258449832321547427568 : (((((((False ∧ p5) ∧ p4) → p2) → p4) ∨ (p5 → (((p5 ∧ p5) ∧ True) ∨ True))) ∨ False) ∨ (p4 ∧ ((((p1 → True) → p2) ∧ p4) → p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118361664627060340478384938421 : ((p2 ∨ (((((((True ∧ p4) ∧ p2) → p1) ∧ True) → (True → (False ∧ True))) ∧ ((True → (p5 ∧ p5)) ∨ False)) ∨ (p5 → True))) ∨ (p3 → False)) := by
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
theorem thm_5_vars_54834948424373285830470576390 : (((p3 → ((p4 ∧ (p1 → (p2 ∧ True))) ∧ p4)) → (p5 → (p2 → ((((p5 ∨ p3) → (((p5 → p5) ∨ p1) ∨ True)) ∨ True) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205061247870043899882550355630 : (((p2 → (p1 ∧ (False ∨ False))) → False) ∨ (True → (((p5 ∨ p5) ∨ p4) ∨ (True ∨ ((True ∧ ((False → (False ∧ (True ∨ p4))) ∨ True)) ∨ p3))))) := by
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
theorem thm_5_vars_792578742264316463408683139332 : (((True → ((p4 → ((((p5 → p1) → p5) ∧ p4) ∨ p5)) ∨ ((p2 ∧ (((True ∧ (p2 ∧ (True ∧ p2))) → p3) ∧ True)) ∨ (True ∨ True)))) ∨ p4) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178444857456641791769260123631 : (((((p2 ∨ (p5 ∧ p2)) ∨ p4) → (p4 ∨ p2)) ∧ (p1 ∧ (p4 → p1))) ∨ (p4 ∨ (((((True ∧ p5) ∧ p2) → (p3 ∨ p1)) ∨ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172456620910107255115725388102 : (((False ∧ ((p2 → p2) ∧ p1)) ∨ (((p3 ∨ False) ∨ p4) ∨ ((True ∨ p1) ∨ False))) ∨ (((True → p4) → (p2 → (p1 ∨ False))) → (True ∧ p2))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260415009572045416855506251496 : ((p3 → True) → (((p2 ∧ (((((p3 ∧ p2) → (p4 → (p3 ∧ (p3 ∨ p2)))) ∨ p1) → (p3 ∧ (False → p2))) ∧ True)) ∨ True) ∨ (p2 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116615795542148969605320888085 : (((False → True) ∧ (p2 → ((p5 → p5) ∧ ((p2 ∨ (p3 → (p4 ∧ (p3 → p4)))) → ((p4 ∨ (True → (False ∨ p4))) ∧ p2))))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735492506476496268128164824624 : ((((p4 ∨ p4) ∧ ((p1 ∨ (p4 ∧ p4)) ∨ (p4 ∨ ((((((((p1 ∧ p5) ∧ p4) ∧ True) → p2) ∨ False) ∧ p5) ∧ p2) ∧ (p4 → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776806663724902755903937879411 : (((p1 ∨ ((((p4 ∨ (p1 ∧ (p4 ∧ p4))) ∧ p5) ∨ ((((p2 → p4) ∨ (p3 ∧ (p2 ∨ (False ∧ p5)))) ∨ p5) ∧ (True → p5))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185191420094308224914306360412 : ((True ∧ ((p3 ∨ ((False ∨ (p4 → (p2 → p5))) → p3)) ∨ p3)) ∨ (False → ((p4 ∨ (p1 ∨ (((False ∨ p1) ∧ p3) ∨ p3))) ∨ (p1 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246732855294802094653634041318 : ((p5 ∧ p5) ∨ (((((p5 → True) ∧ ((((((p2 → (p3 ∧ False)) → p3) ∨ p1) → p5) ∨ True) ∨ p2)) ∨ (False → (False ∨ False))) ∨ p2) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22178190729683500149262447767 : ((((True → True) → (((p1 → p3) → False) ∨ p4)) ∨ (True ∨ (True ∨ (p4 ∧ ((False → ((False → (p5 ∧ True)) → p3)) ∨ (True ∨ False)))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215325784587659051566036116795 : ((p1 ∧ (p5 ∧ (p3 ∧ p3))) ∨ (p3 ∨ ((False ∧ (((((True → p2) ∧ (False ∨ (p4 ∨ False))) ∨ ((False → p2) → True)) → False) → p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194790160031471535786674930287 : (((False → (False ∨ ((p4 → p5) → p2))) ∨ p2) ∧ ((p4 → ((p2 → (((p1 → p1) ∧ (p3 ∨ (p1 ∧ p1))) ∨ False)) ∧ (p4 ∨ p5))) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336246357254913724206730586920 : (p1 → ((((((p5 ∨ ((p4 ∧ p1) ∧ p3)) ∨ p2) ∨ False) ∨ (((False ∧ (False ∧ True)) ∧ p2) → True)) → (p2 ∨ (True → (p5 → p3)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683700410632030808059556666734 : (((((False ∨ ((p2 ∨ ((p3 ∧ True) ∨ p5)) ∨ (p4 → (((p4 ∧ p3) → p5) → p3)))) ∧ p4) ∨ (((True ∨ p4) ∨ (p4 → p5)) ∨ p2)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252936694620601373403239368020 : ((True ∧ p2) → ((p5 ∧ (((p1 ∨ True) ∨ ((True ∨ p1) ∨ (((False ∨ (((p3 ∧ True) ∨ p1) ∧ False)) → (False ∨ p4)) ∧ p2))) → False)) ∨ p2)) := by
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
theorem thm_5_vars_259265070818356007545804265228 : ((False → p1) → (((False ∧ (((False ∨ (False → p2)) ∧ p5) → ((p5 ∧ ((p2 → p1) → (p4 → True))) → p1))) ∨ True) ∨ ((True → p3) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148257704418042868265979918464 : (((p3 ∧ ((p5 ∨ (p3 ∨ (p1 ∨ ((False → (p4 → (p2 → False))) ∧ p4)))) ∧ True)) ∨ ((True → False) → p1)) ∨ (p1 ∧ (p3 → (False ∧ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258590761181889835502013238274 : ((p5 ∨ p4) → ((True → (((p1 ∧ ((False ∨ (False ∨ ((True → p3) → (p3 → (((p5 → False) ∨ True) ∨ p1))))) ∨ False)) → p1) ∧ False)) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196852071914379423357334727649 : (((False ∨ (False ∨ ((True → False) ∧ p5))) ∧ p5) ∨ (False → (((p5 → (p4 ∨ (p1 ∧ (((True ∨ p2) ∧ p1) ∧ p1)))) ∨ (p1 → False)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50075020863647974087386282027 : ((((p5 → p1) → (p1 → (((p5 ∧ ((False ∨ (p3 → p3)) ∨ p3)) ∨ (True ∧ p3)) ∨ (p1 ∧ p4)))) ∧ (p4 ∨ (p5 ∧ (p2 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109174431605842381928258215952 : ((False ∨ (((((p1 ∧ False) ∨ (p1 → p2)) → ((p2 → (p2 ∧ p1)) ∧ (p5 ∧ (((p1 → False) ∨ p1) → p4)))) → p1) ∨ True)) ∧ (True ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299463732096167803804415240710 : (False ∨ ((p5 ∨ ((p1 ∧ ((False → (((p2 → True) → p5) ∧ True)) → (p3 ∨ (False ∧ True)))) ∧ (((False ∨ (p5 ∧ p2)) → p5) → True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248309049132816672432796628423 : ((p2 ∨ p2) ∨ (p3 → (((((p4 ∨ (True ∨ ((True ∨ p5) ∨ True))) ∧ p2) ∧ True) → (p4 ∧ p5)) ∨ ((((p2 ∨ p5) ∨ True) → p3) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172464664237349929728989626245 : (((True → (p5 ∨ (p2 → p5))) ∨ ((p4 ∧ (False ∧ (False ∨ (p4 ∧ p5)))) ∨ p3)) ∨ ((True ∨ (p4 ∧ False)) → (p3 → ((p1 ∧ p2) → p2)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651933963694461136332976346077 : (((((p4 → p5) → ((p3 → ((p2 ∨ p2) ∨ ((((p3 → p4) ∧ p2) ∧ (False → True)) → p5))) → ((p2 ∧ p2) ∧ p5))) ∧ (False → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264277766073265370172127599377 : (True ∧ ((p2 ∧ (((p1 ∨ False) → False) ∧ p4)) ∨ (((True → False) ∨ (True ∧ (p2 ∨ ((((p5 ∨ p2) ∧ p5) ∨ p4) → (p5 → True))))) ∨ p4))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158115071795808660701376422583 : (((p2 ∧ (p2 ∨ (False ∨ True))) ∧ (p5 ∨ (((p3 ∧ (p3 ∨ p2)) → ((True ∨ p1) ∨ False)) → p2))) ∨ (True ∧ ((p4 ∧ p1) → (True ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65978377778693874714569712048 : ((p4 ∨ (p1 → ((((p1 → (((p4 ∨ p4) ∧ (False ∧ (p5 → p4))) ∨ (p4 → ((True ∧ p3) ∧ (p3 → p3))))) ∧ p2) → False) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738544621706063796802538672655 : ((((p1 ∧ p5) ∨ ((False ∧ (((((p5 → p4) → (((((p3 ∧ p2) ∧ True) → (p1 → True)) ∨ p2) → p1)) ∧ False) ∨ p1) ∧ p2)) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_44824295492512700712683543303 : ((((p2 → (p2 ∨ p2)) ∧ (p5 ∧ (((False → p3) ∧ (p2 ∨ True)) ∧ (p4 → ((((p4 ∧ p3) → False) → p4) → (False ∨ p4)))))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200464405250516495028205109576 : (((p3 → p1) ∨ (p5 ∧ ((False → p3) ∧ p5))) → ((((p1 → True) → (p5 ∨ False)) ∧ p2) → ((p2 → (False ∧ (p5 ∨ p2))) ∨ (p3 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149810752633887997358004863646 : ((False ∨ (p4 → (((p1 ∧ True) ∧ ((True → (p5 ∨ ((((p3 ∨ p5) → p4) ∧ True) → p5))) ∧ p4)) ∨ p4))) ∨ (p3 ∨ ((True ∧ p3) ∧ p3))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670118522421029439218034508599 : ((((((p3 ∧ ((False ∨ p5) ∧ p3)) ∨ p2) ∨ (((p3 → (p2 → p4)) → ((p2 ∧ (False → p4)) ∨ False)) ∨ p1)) ∨ (False → (p5 ∨ p5))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48585465225364981856583173561 : (((((((True → ((p5 ∨ (p1 → (p1 ∧ p2))) → False)) ∨ p2) ∧ ((p4 ∧ p1) ∨ p2)) ∨ p3) ∧ (p5 ∧ p4)) ∧ (p5 ∨ (False ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249448590993438112623772932842 : ((p5 ∨ False) ∨ (True ∧ ((p4 ∧ (p2 ∨ True)) ∨ ((((True ∨ p4) ∧ (((False → p2) ∨ (True ∨ p2)) → False)) ∨ (p4 ∧ (False ∧ p5))) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h6 : ((False → p2) ∨ (True ∨ p2)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h7 := h4 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h9 : ((False → p2) ∨ (True ∨ p2)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h10 := h4 h9
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683955546066487979782018418023 : ((((((p2 ∧ ((((p1 ∨ ((p1 → p2) → p4)) ∨ (p4 ∧ p4)) ∨ False) ∨ p3)) → p1) → p4) ∨ ((p1 → False) → (p4 → (p5 ∨ p4)))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49355940966588367917571879193 : (((p2 → ((p5 ∧ (((((p4 → p2) → p1) ∧ (p2 ∧ p5)) ∨ ((p1 ∧ p2) ∨ p1)) ∨ p5)) ∨ (p1 ∨ p4))) ∨ ((p5 → p4) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68184884198950674828829143691 : ((p3 → (((((((p4 ∧ True) ∨ p1) ∨ ((True → True) ∧ p5)) → False) → ((p5 ∨ ((p3 → False) → p1)) ∨ p3)) → (True → p1)) ∨ p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263974104304605681257670758980 : (True ∧ (((p3 ∨ (p2 ∧ ((((p1 → p2) → p4) ∨ p4) → p5))) ∨ True) ∨ (p1 ∨ (((((p5 ∧ p1) ∨ p4) ∨ (p2 ∨ p1)) ∧ False) ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757304940184383986922558993031 : (((p1 ∧ ((p1 ∨ p3) ∨ ((((True → ((p5 ∨ (((p5 ∧ p3) ∨ p1) ∧ (p2 → True))) ∧ (p3 → (p1 ∨ p2)))) ∨ p2) ∨ p4) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259582187814356151493238396478 : ((p1 → True) → (((p5 ∧ True) ∧ (True → True)) → ((((((p1 ∧ p1) ∧ ((False → p5) ∧ p3)) ∧ False) ∧ p1) ∨ (p5 ∨ p2)) ∨ (p2 ∧ p4)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205952161563300355469341152423 : ((False ∧ (p3 ∨ ((False ∧ p5) ∧ p1))) ∨ (p5 → (((((p5 ∧ p1) ∨ p3) ∧ ((False ∧ (p2 ∧ (False ∧ p5))) ∧ p1)) → True) ∧ (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320140335938725951411836084455 : (p4 ∨ ((p5 → (p2 ∧ p1)) → ((((p2 → (((p2 ∧ p4) → ((p3 ∧ (True → (p2 ∨ (p2 ∧ p1)))) → p1)) ∨ True)) ∨ p3) ∨ p4) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693614677163732367041756201206 : (((((((p2 ∨ (p4 ∧ p5)) → (((p1 ∨ p2) ∨ p2) → p3)) ∧ p2) ∨ p1) ∨ (((p4 → p4) → p4) → (p2 ∨ (p3 ∨ (True ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205642237359786238405009718452 : (((p4 ∧ p4) ∨ (p2 ∨ (True → p1))) ∨ ((p5 → (False ∧ (((True ∧ False) ∧ ((p2 ∧ True) ∨ (p1 ∨ p3))) ∧ p2))) ∨ ((True ∧ True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155562199012666230571606057391 : (((p3 ∧ (p2 → p2)) → ((p4 ∧ (p1 ∧ ((p3 ∧ (p2 ∧ (p2 ∨ (p3 ∧ False)))) ∨ p4))) ∨ True)) ∧ ((False → p3) ∨ (p4 ∨ (True ∨ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350277194205087605384158503215 : (p4 → ((p5 ∧ (((p5 → (((p1 ∧ True) ∧ p2) → (p2 → p5))) → (((p5 → ((True ∧ p4) → p4)) → False) ∨ False)) ∨ (p2 → p5))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37970735336102604639759804873 : (((((p5 ∨ ((p1 ∨ (p3 ∨ (p1 ∧ p1))) ∧ (((p2 ∨ p3) ∧ ((True → True) → (p4 → p1))) → p2))) → p5) ∨ (p2 ∨ p5)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40913454383271746010407199186 : ((((p1 ∨ ((True ∧ ((p2 → (False ∧ True)) → (True ∧ (p5 ∧ p2)))) ∨ (((p5 ∨ p1) ∧ p1) ∧ (True ∨ p2)))) ∧ (p3 → p2)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225493584380911483523192752843 : (((p5 ∨ False) ∧ p5) ∨ (p3 → (p4 → ((((p4 ∧ (((True ∨ (p5 ∨ ((p4 → p1) ∧ p3))) → p5) → p1)) ∨ p2) → (p3 → False)) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38290573885890105651474736700 : ((((p4 ∧ (p1 ∨ (p4 → (((False → p2) ∨ (((True ∧ False) ∧ p4) ∨ True)) ∨ (False ∨ p2))))) ∨ (p2 → ((False → True) → False))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45173990467668388691300943098 : (((True ∧ ((p1 ∧ True) → ((((p2 → (p4 → (((p4 ∧ ((p5 → False) ∨ False)) ∨ p1) → p5))) → p3) ∧ p4) → (p3 ∧ p1)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263209446960185528575070824026 : (True ∧ (((((p3 ∧ (True → False)) → ((((p4 ∨ p4) ∨ ((False ∧ p1) ∨ p2)) ∧ p2) ∨ p1)) ∨ ((False ∨ p2) ∧ False)) → p3) → (p3 ∧ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 ∧ (True → False)) → ((((p4 ∨ p4) ∨ ((False ∧ p1) ∨ p2)) ∧ p2) ∨ p1)) ∨ ((False ∨ p2) ∧ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (((p3 ∧ (True → False)) → ((((p4 ∨ p4) ∨ ((False ∧ p1) ∨ p2)) ∧ p2) ∨ p1)) ∨ ((False ∨ p2) ∧ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- False on the left can always be used.
    apply False.elim h14
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h9
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178838767313215815625021471038 : ((((p2 ∨ True) ∨ True) → (((p2 → True) → False) ∧ (p1 → (p5 → p4)))) ∨ ((p4 ∧ (((p2 → False) → p1) ∨ True)) → ((p1 ∨ p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51308714877360132174937411993 : (((p2 ∨ ((p1 → p2) ∧ ((p1 → p5) → ((((p5 ∨ p2) ∨ p2) → p5) → (p3 ∧ p1))))) ∨ (p1 ∨ (False → ((p3 ∧ p2) ∨ p3)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637566199082091635688768452660 : ((((((((p1 ∧ (False → p5)) ∨ p3) → True) → (True ∧ p2)) ∨ ((True ∧ False) → (((p3 ∧ p4) ∧ (p4 ∧ (p4 → True))) → p2))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247584509991894525512471351089 : ((False ∨ p5) ∨ (((p2 ∧ ((((True → p1) → p3) ∨ (((p5 → (p2 ∨ p5)) ∨ False) ∨ (p3 → True))) ∨ p4)) ∨ (p1 → (p4 → p4))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136069133261434489546578848672 : (((((p2 ∨ False) → p1) → (p2 ∧ (p3 ∧ p3))) ∧ ((p5 → p3) ∨ ((True ∨ ((p2 → (p5 ∧ p4)) → p1)) ∨ p4))) ∨ ((p2 ∨ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68077552461325840439352391111 : ((p2 → (p3 ∨ ((p4 ∨ (False ∨ (((True ∨ (p3 → (p2 → ((p5 → ((True ∨ p5) ∨ True)) ∧ p5)))) ∨ True) → p5))) ∨ (True ∨ p4)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249835133560453376557942025874 : ((True → False) ∨ (((((((p3 ∧ p1) ∧ p5) ∨ True) ∨ ((((True ∧ p2) → p5) ∧ (p1 ∨ False)) ∧ (p4 ∧ p5))) ∨ (p2 → p3)) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_947606911974975337367657079453 : (((((True ∨ p2) ∨ (p2 ∨ p5)) → ((((p1 → (p5 → True)) ∨ p3) ∧ p4) ∧ (p4 ∧ ((p5 ∨ (False → p5)) ∧ ((p3 ∧ False) ∨ False))))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∨ p2) ∨ (p2 ∨ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62242201455156834128644117225 : ((p3 ∧ (((True ∧ (True ∧ (p5 ∧ True))) ∧ (p1 ∨ (((False → ((((p3 ∨ p5) → True) → (p1 → p1)) → p3)) ∧ False) ∨ p3))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354531315541034189432004704104 : (p5 → ((p1 → (((True → (p2 → ((p4 → (True ∨ (False → (p2 ∨ ((p4 → p5) ∧ (p3 ∨ p5)))))) → p4))) ∨ False) ∨ (False → p2))) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307624408168618479027829495655 : (p1 ∨ (p1 → (((True ∨ True) ∨ ((p5 ∧ ((p2 ∨ p4) ∨ (p3 → False))) ∨ (p1 → (p1 ∨ (p4 → False))))) → ((False ∨ True) ∧ (p1 ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
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
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h24 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h1
      case inr h25 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h26 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262474458426650977674000311653 : (True ∧ ((p4 ∨ ((p2 → ((p4 ∨ p1) ∧ p3)) ∧ (((p5 → p4) ∧ p5) ∨ (((False ∧ ((p2 ∧ (p2 ∨ p5)) ∨ p4)) → False) ∧ p1)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301171745069178177131097258983 : (False ∨ ((((p4 → (p5 → p2)) → (p2 → True)) ∨ p2) → ((p2 ∧ (True ∧ ((p5 ∧ (p4 → (p2 → False))) ∨ p2))) → ((p3 → p3) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
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
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  -- Conjunctions on the left can always be decomposed.
  let h16 := h2.left
  let h17 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h17.left
  let h19 := h17.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h23 =>
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h24 =>
      -- One of the premise coincides with the conclusion.
      exact h24
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h26 =>
      -- One of the premise coincides with the conclusion.
      exact h25
    case inr h27 =>
      -- One of the premise coincides with the conclusion.
      exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197668798039846769023348344948 : ((((True ∨ p3) → (True ∧ p3)) → (p5 ∨ p4)) ∨ ((p1 → ((p1 ∨ (p4 ∨ ((((False ∧ (p4 → p2)) ∨ p2) ∧ False) ∨ p1))) ∨ p5)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147959290283106747997515249196 : (((False ∨ ((p2 ∨ (True ∧ ((p1 → (p4 ∨ p3)) ∨ p1))) ∨ (True ∨ ((p2 → p3) → True)))) ∧ (p5 → True)) ∨ (p5 ∨ (False ∧ (p2 → False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203751482658897357840067572708 : ((p5 ∨ ((p4 ∨ p4) ∨ (True ∧ True))) ∧ ((p2 → p1) → (p1 → (p1 → (p1 → ((((True → p1) → p1) ∧ ((False ∧ p3) → p3)) ∧ p1)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164610586945261486201559346288 : (((p2 ∧ (((False → (((True ∧ False) → (p3 → (p1 → True))) ∧ True)) → True) ∧ p2)) ∧ p2) ∨ (((p5 ∨ False) ∨ ((p2 ∨ False) → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46347340987458770350836871168 : ((((p1 ∧ ((False ∧ ((((p2 ∧ True) → p2) ∨ p3) → p2)) ∨ (p1 → True))) ∨ ((p3 → (True ∧ (False ∧ p1))) ∧ p2)) ∧ (p5 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186316353350825740067265033694 : ((((p5 ∨ ((p2 ∧ (p2 ∧ p3)) ∧ True)) ∨ (p3 ∨ True)) → False) → (((p1 ∨ p1) ∧ p2) → (((True → (p1 ∨ p2)) ∨ p4) → (p3 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : ((p5 ∨ ((p2 ∧ (p2 ∧ p3)) ∧ True)) ∨ (p3 ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h11 : ((p5 ∨ ((p2 ∧ (p2 ∧ p3)) ∧ True)) ∨ (p3 ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h12 := h1 h11
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h2.left
    let h15 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h17 : ((p5 ∨ ((p2 ∧ (p2 ∧ p3)) ∧ True)) ∨ (p3 ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h18 := h1 h17
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h20 : ((p5 ∨ ((p2 ∧ (p2 ∧ p3)) ∧ True)) ∨ (p3 ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h21 := h1 h20
      -- False on the left can always be used.
      apply False.elim h21
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h2.left
    let h24 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h25 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h26 : ((p5 ∨ ((p2 ∧ (p2 ∧ p3)) ∧ True)) ∨ (p3 ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h27 := h1 h26
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h29 : ((p5 ∨ ((p2 ∧ (p2 ∧ p3)) ∧ True)) ∨ (p3 ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h30 := h1 h29
      -- False on the left can always be used.
      apply False.elim h30
  case inr h31 =>
    -- Conjunctions on the left can always be decomposed.
    let h32 := h2.left
    let h33 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h32
    case inl h34 =>
      -- One of the premise coincides with the conclusion.
      exact h31
    case inr h35 =>
      -- One of the premise coincides with the conclusion.
      exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116048720304436707678919321216 : (((p1 → (p4 ∧ (True ∧ True))) → ((((p5 → (p1 → p3)) ∧ ((p2 ∧ (p2 ∧ p3)) ∧ p1)) → p5) → (p4 ∨ (p1 → p1)))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149890767899836708877786678243 : ((p2 ∨ ((True ∧ p3) → (((p1 → ((False ∧ (p1 ∧ False)) ∨ p2)) ∧ (p3 ∨ p1)) ∨ ((False ∨ p1) → p4)))) ∨ ((False ∧ (p2 → True)) → p1)) := by
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
theorem thm_5_vars_247772665339548142331318236099 : ((p1 ∨ p1) ∨ (((((p5 ∧ p3) ∧ (True ∧ ((p3 ∨ (False ∧ (p3 → False))) → p2))) ∧ p3) ∨ (p4 ∧ (True ∨ (p3 → (p3 ∧ p4))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173417157861289435346516012304 : ((p5 → ((((p1 → (p4 → p3)) ∧ p5) → (True → p3)) ∨ ((False ∨ p1) ∧ p3))) ∨ (p2 ∨ (((False ∧ p2) → False) ∨ ((p1 ∨ p2) ∨ p1)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48760234831550303403087871713 : ((((True ∧ False) ∨ ((((p1 ∧ ((p1 ∧ ((True ∧ (False ∨ p5)) ∨ p4)) → p4)) ∧ (p1 → p4)) → p4) ∨ False)) ∧ (p4 ∨ (p3 ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59391220458018633705990113461 : (((True → p1) ∨ (((((p3 → (p2 ∧ p3)) ∧ False) ∨ (p1 ∨ (p3 ∧ ((p5 → p4) → (p1 ∨ False))))) ∨ True) ∨ ((p5 → p4) ∧ p5))) ∨ p4) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358714003728402480946080367137 : (p5 → (p5 → ((((p2 ∨ (((False ∧ True) ∨ (p5 ∧ False)) → (p1 ∧ (p3 ∨ True)))) → p4) ∨ (p2 ∨ (p1 ∧ (p5 ∨ p3)))) ∨ (p3 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



