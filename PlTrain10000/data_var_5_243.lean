variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354347502848733891919439318895 : (p5 → (((True ∨ ((((p3 → (p1 ∧ p3)) → p3) → p5) → False)) ∧ (((((p3 ∧ True) → p5) ∧ True) → (p3 ∧ (p3 ∧ p3))) ∨ p5)) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172193746275297391247995847167 : ((((((p1 ∨ True) ∧ ((False ∧ p2) ∧ p3)) ∨ p5) ∨ p5) → ((p3 ∧ p1) ∧ p3)) ∨ (p3 ∨ ((False → (True ∨ ((p2 → p4) → p1))) ∨ p5))) := by
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
theorem thm_5_vars_355629292545300943008106259263 : (p5 → ((p3 ∨ ((p5 ∧ (p4 ∨ p1)) ∨ ((p3 ∨ (p1 → ((True ∨ (False → p5)) ∧ False))) ∨ (p4 → ((True → p1) → p3))))) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228270884546217402367095530143 : ((p5 ∧ (p4 → p5)) ∨ (((p4 ∨ p4) → (((p2 → (p5 → p3)) → p2) ∨ (True ∧ (((True → p2) ∨ (p3 → False)) → p1)))) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244719967422085248517913443414 : ((p1 ∧ True) ∨ (p2 ∨ (p1 → ((p4 ∨ p2) ∨ (((p2 ∨ p1) ∧ (((p2 ∨ (p4 ∨ (False ∧ p5))) → p5) ∧ p2)) → (p5 ∨ (True ∨ p4))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h4.left
    let h10 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_855960729637764270310302935997 : (((((((p2 ∨ (p5 ∨ ((((True ∧ ((True ∧ p5) → p2)) → p1) ∨ False) → (p1 → p4)))) ∨ (p1 ∧ p2)) ∧ (True → True)) ∨ True) → False) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p2 ∨ (p5 ∨ ((((True ∧ ((True ∧ p5) → p2)) → p1) ∨ False) → (p1 → p4)))) ∨ (p1 ∧ p2)) ∧ (True → True)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80939911934591301344548715148 : ((((p4 ∨ ((((p2 → ((p4 ∧ ((p5 ∧ p2) ∨ p2)) → ((p2 ∧ p4) ∨ p5))) → p1) ∨ p4) → True)) → False) ∧ (True ∨ (p3 ∧ p1))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p4 ∨ ((((p2 → ((p4 ∧ ((p5 ∧ p2) ∨ p2)) → ((p2 ∧ p4) ∨ p5))) → p1) ∨ p4) → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : (p4 ∨ ((((p2 → ((p4 ∧ ((p5 ∧ p2) ∨ p2)) → ((p2 ∧ p4) ∨ p5))) → p1) ∨ p4) → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h11
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180796293256050608902917021850 : (((p5 → (p1 ∨ (p4 ∨ True))) → ((True ∧ p1) → ((p1 → p3) ∧ p3))) → ((p3 ∧ (True → True)) ∨ (False ∨ ((p3 ∧ p1) → (p4 ∨ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677817105409968250873160632800 : ((((((p5 → (p2 ∨ ((((p5 → ((True ∨ p4) → p4)) ∨ p1) → p5) ∨ p5))) → p2) ∧ (p4 ∨ p4)) ∨ (((p3 ∨ False) ∨ False) → p3)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347591184798351322301043793785 : (p3 → ((((p4 → p5) → p4) ∧ p1) ∨ (((p1 ∨ (False → p5)) → p2) → ((False → p5) → (p3 ∧ ((((p4 ∨ p5) ∨ p3) ∨ p3) → p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h8 : (p1 ∨ (False → p5)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h9
          -- False on the left can always be used.
          apply False.elim h9
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h10 := h2 h8
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h12 : (p1 ∨ (False → p5)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- False on the left can always be used.
          apply False.elim h13
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h14 := h2 h12
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h15 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h16 : (p1 ∨ (False → p5)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- False on the left can always be used.
        apply False.elim h17
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h16
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h20 : (p1 ∨ (False → p5)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- False on the left can always be used.
      apply False.elim h21
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h22 := h2 h20
    -- One of the premise coincides with the conclusion.
    exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215897802430619380656801387283 : ((p3 ∨ ((p1 → p3) ∨ False)) ∨ (((p5 ∨ (False → False)) → ((p4 ∨ False) ∨ ((((p1 → p5) ∨ (p5 → (p2 → False))) ∨ p5) ∨ True))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53749479555786766718426983096 : (((((((p4 ∧ p5) → (p3 ∧ p4)) → False) → p1) ∧ p1) ∨ (p5 → (((p2 → (p4 → ((p1 → p5) → p3))) ∧ p1) → (p2 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209561215023057862705691563952 : ((p5 → ((p2 → (p5 → p3)) ∨ p3)) → (p4 → ((p2 ∧ (p5 ∨ p2)) ∨ ((True → False) ∨ (p4 ∨ ((True ∨ (True ∨ (p5 ∧ p3))) ∨ p2)))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114158695079683447721512010494 : (((((p5 ∧ ((((False ∨ p3) ∧ p1) ∧ (True ∧ (p1 ∨ ((p1 → p2) → False)))) → p5)) ∨ True) → False) → (p4 ∨ (False ∧ False))) ∨ (p2 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ ((((False ∨ p3) ∧ p1) ∧ (True ∧ (p1 ∨ ((p1 → p2) → False)))) → p5)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136770579164212867616506715485 : (((p5 ∨ False) ∧ (((p3 ∧ (((p1 ∨ True) → True) ∧ False)) ∧ ((p4 ∨ (p4 → p5)) → (True ∧ p1))) ∨ (p2 ∧ False))) ∨ (p2 ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113224643191912273276292238453 : (((((((False ∨ p1) → False) ∨ (((p1 → p2) → (p3 → ((p5 ∧ (p4 ∧ p3)) ∨ p2))) ∨ True)) → p3) → False) ∧ (False ∧ p5)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683609051564797311600175327099 : (((((((p4 ∧ ((p4 → p5) ∨ p4)) ∧ (((p3 ∧ p1) ∧ p4) ∨ False)) ∧ (p2 ∨ p1)) ∧ p4) ∨ (p2 → ((p4 → p1) ∧ (p1 ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47505543313977576293316923955 : (((p2 ∨ (((p3 ∧ ((p4 ∧ False) ∨ ((((p5 ∨ False) ∨ (p3 ∨ False)) → p1) → True))) ∧ ((p4 ∧ p5) ∨ p2)) ∧ p2)) ∨ (p2 ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261208702202253207676672192815 : ((p4 → p5) → ((((p2 → p5) ∨ (False ∧ ((p1 ∨ p1) ∨ (p4 ∧ True)))) → (p4 ∨ (((True ∨ p2) → p1) ∨ p5))) ∨ ((True → True) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_949146191148256373752917803933 : (((((True → p2) ∧ p2) ∧ ((True ∧ (((p5 → (p3 ∨ p2)) ∧ False) ∧ (p2 → (p3 → ((p1 → p3) ∨ True))))) → ((p2 ∧ p2) → p3))) → p2) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600109514456823786300589555082 : (((((p4 ∨ p2) → (((p3 ∧ p4) ∧ (p4 ∧ (p2 ∧ ((p1 → ((p1 ∧ (p3 ∨ False)) → False)) ∨ (False → (p4 ∨ p4)))))) → p1)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743085667586893645912791346383 : ((((p4 → p1) ∨ ((((p5 ∧ (p3 ∧ p5)) ∨ (p1 → False)) ∧ p5) → (((False ∨ (p1 → ((p2 → False) ∧ p5))) → p2) ∨ (p1 → p1)))) ∨ p1) ∧ True) := by
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
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233106841938243693301558752325 : ((p4 ∧ (p3 → p5)) → (((p3 → (((p1 → p4) ∧ (p1 ∨ (p2 → p3))) → ((p5 → p1) ∧ p4))) → False) ∨ (((p4 ∧ p4) ∨ p5) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45113421450970807498558754389 : ((((p3 ∨ p5) → (p5 ∧ ((p4 ∨ (p1 → p1)) → ((((True ∨ ((p1 → p2) ∧ p2)) ∨ ((p3 → p4) → p3)) ∧ p4) ∧ p2)))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697057589880250528198092960122 : (((((((p1 ∧ False) ∨ True) → (p5 → p3)) → (p2 ∧ (True → p3))) ∧ (p2 → ((p3 ∧ p2) ∨ (p2 ∨ (p5 → (True ∨ (p2 ∨ p2))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742406142434630212054267536701 : ((((p1 → p5) ∨ ((False ∨ (p1 ∨ (((True → p2) ∨ p3) ∨ ((((False ∨ p4) → p4) ∧ True) ∧ ((p4 → (p3 ∨ p5)) ∨ p4))))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171722342506994811177436299071 : (((((((p1 ∨ True) ∧ p5) → True) ∧ (p5 → (p5 ∨ (p2 ∨ p5)))) ∧ p2) → p1) ∨ (p2 ∨ (p2 ∨ ((p5 ∧ False) → ((p5 ∨ True) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743552030291378783067425622965 : ((((True ∧ True) → ((((((p1 ∨ False) ∧ p1) ∧ (False ∧ p2)) ∨ (((True → p1) ∧ (p1 ∧ p1)) ∧ p4)) ∨ p5) ∨ (p3 ∨ (p4 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184825043222236660461673339096 : ((((False ∧ (p3 ∧ True)) → p2) → (p2 ∧ (False ∨ (p4 → p5)))) ∨ ((True → p3) ∨ (p5 ∨ (((p2 → (p3 → True)) ∨ p4) → (p1 → p1))))) := by
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
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166860557957729234809893574314 : ((((p1 → (((((p1 → ((p2 → p1) → p2)) → p5) → False) ∧ False) ∨ p3)) → p2) ∧ p3) → ((False ∧ (p3 ∨ (True → (p3 ∨ True)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p1 → (((((p1 → ((p2 → p1) → p2)) → p5) → False) ∧ False) ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118398076907857306350507533051 : ((p2 ∨ (((True ∧ p3) ∧ p3) → (p4 ∨ ((((p4 ∨ p1) ∨ ((p4 ∧ False) ∨ True)) ∨ p4) ∧ ((True ∧ (p5 ∧ p1)) ∧ p1))))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49106623819721727628130943605 : (((((p1 ∧ ((p5 → (p5 ∨ ((True ∨ p5) → (True ∧ p1)))) ∧ p3)) ∨ p2) ∧ (p3 ∧ ((p2 ∨ True) ∧ True))) ∨ ((False → p5) ∨ p2)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40876341658498968902145405638 : (((((((False → ((p3 → (False → False)) ∧ (p2 → (p4 ∧ (True → p2))))) → p1) ∧ p2) ∧ (p4 → (p3 ∧ True))) ∧ (p4 ∧ p4)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341717202013284362049434034585 : (p2 → (((p1 → (((True ∧ (p2 ∨ p1)) ∨ (False ∨ False)) → p2)) → (p5 ∨ (((p5 → p1) ∧ p2) ∨ ((p5 ∨ True) ∨ p2)))) ∨ (p2 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330780220638980182490231668927 : (True → (p2 → (((((p2 ∧ (p4 ∨ (((p4 → (((p1 ∨ p2) ∨ p3) → (False → p2))) ∨ p1) ∨ p2))) ∨ p4) → (p4 ∧ True)) ∧ p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209074023280611163577091428055 : ((p1 ∨ (p4 ∨ ((p4 ∧ False) ∧ p3))) → (((p2 ∧ (True ∨ p2)) ∨ False) ∨ (p3 ∨ (((True ∨ ((p2 ∨ p5) ∧ True)) ∨ False) ∧ (False → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
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
      intro h6
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
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665068237429685667820426524816 : ((((p5 → ((((p5 → ((False ∨ p2) → p3)) → p4) ∧ ((((p4 ∨ (p3 → (False ∨ True))) ∧ p1) ∨ p5) → p2)) ∨ False)) → (False ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206354995276625692661095469944 : ((p2 ∨ ((p2 ∨ True) ∧ (p2 ∨ False))) ∨ (((((False ∨ p3) ∧ ((p1 ∧ (p4 ∨ p2)) → ((p2 → p4) → p1))) ∧ p3) → False) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184698225996676774454275771826 : ((((((p1 → p1) ∧ p4) ∧ p1) → False) → ((p3 ∧ p3) ∧ p3)) ∨ (p2 → (p3 → (((False ∨ ((p4 ∧ p5) ∨ p5)) ∧ False) → (True ∨ p5))))) := by
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
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h5
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785934955200602991900986679355 : (((p4 ∨ ((p4 → (p4 ∧ (p5 ∨ (((False → ((p3 ∨ p5) ∨ p4)) ∨ (p5 ∧ ((p2 ∨ True) → True))) → (p1 ∧ True))))) ∧ (True ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41986325854826329479361507453 : ((((p4 ∨ p4) ∧ ((p1 ∧ (p4 ∧ (((p1 ∨ (((p4 ∧ p1) → p5) → p1)) ∨ p1) → p5))) → (((True ∨ p1) ∨ p3) → p3))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64389430841456709695321628776 : ((p1 ∨ (((((False ∧ (((p1 → (p2 → p1)) → (p1 ∧ p5)) ∧ (p4 ∨ (True ∨ True)))) → (p4 → p1)) ∧ (p4 ∨ p1)) ∨ p5) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166440570521209659498519434550 : ((p2 ∨ ((p1 ∧ ((p5 ∧ ((p5 → (p5 ∧ True)) ∧ (p4 ∧ (p1 ∧ p2)))) ∨ p5)) ∧ p4)) ∨ (((False → (p2 ∧ p4)) ∧ (p2 → True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195296615424589934889780136882 : ((((p3 ∨ (False → p1)) → p4) → (p1 ∨ p4)) ∧ ((p4 ∧ p1) → (((p5 ∨ p1) ∧ ((True → p1) → p1)) → (p2 ∨ (p1 ∨ (p4 ∨ p2)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h5.left
    let h11 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h5.left
    let h14 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655658010697602634737510523091 : (((((((((True ∨ ((p5 ∨ p4) ∧ p2)) ∨ False) ∨ (True ∨ (p3 → (True ∧ p1)))) ∨ p3) → p3) ∧ ((p5 ∧ False) ∨ False)) ∨ (p2 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347020190201792034882972411468 : (p3 → (((p5 → p5) ∧ ((p4 → ((((p1 → False) ∧ p5) → p5) → (p2 ∧ p2))) ∧ p3)) ∨ ((p4 ∨ (p2 → ((p5 ∨ False) ∨ p4))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160947232195806557629097800289 : ((((p5 → False) ∧ p5) ∧ (False ∨ (((p1 ∨ p3) ∧ (p4 → (p2 ∨ ((True → p2) → False)))) ∨ True))) → ((p3 ∨ (p2 ∧ (p4 → p1))) ∨ p3)) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h12 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h13 := h4 h12
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h15 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h16 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h17 := h4 h16
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190816185775356418253826378454 : (((p2 ∧ ((p1 ∧ p2) ∨ (p4 → p4))) ∨ (True → p3)) ∨ ((False ∧ ((True → (p4 ∧ p1)) → (((p5 ∧ False) ∨ True) ∧ p4))) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14798895187887495231579751341 : ((((True → (((False ∧ (p4 ∨ p4)) ∧ ((False ∨ p5) ∨ (p5 ∨ p5))) ∨ (p1 ∧ p2))) → (((p1 ∨ p4) → p5) ∨ p4)) ∨ (p5 → True)) ∧ True) := by
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
theorem thm_5_vars_115832673818545052105637137692 : (((True ∧ ((False ∨ p2) ∨ False)) ∧ (((True → (p2 ∧ False)) ∨ ((p4 → (True ∨ (p3 ∧ p3))) → (False ∧ (p3 → p2)))) ∧ p1)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167563668973230191007834147464 : ((((p4 → (False ∧ (p2 → ((False → (p3 → (p1 ∨ True))) ∨ p2)))) → p3) ∨ (p1 ∨ p1)) → (((True ∨ ((True ∨ p4) ∨ p2)) → False) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632075963410362183126301083378 : ((((((False → False) ∧ (False ∧ (p5 ∨ ((p1 ∧ ((p2 ∨ p1) ∧ p3)) → (p2 → ((((p4 ∧ p5) → p1) ∧ p5) ∧ p3)))))) → True) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336246628803901410550219495756 : (p1 → ((((((p5 ∨ p2) → p3) → p2) ∧ ((p2 ∨ False) ∧ ((p4 → (p2 ∧ p4)) ∧ (False ∨ p5)))) → (p4 ∧ (p2 ∧ (p1 → p1)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187533221829303900861580320799 : ((p1 ∨ (p5 → (p3 ∧ ((p1 ∨ (p3 ∨ p4)) → (p3 ∨ p5))))) → (p3 ∨ (((False → p1) → False) → ((p4 → ((p2 ∨ p1) ∧ True)) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (False → p1) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : (False → p1) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h9
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149997610207078241940734998428 : ((p4 ∨ (p4 → ((((p4 ∧ (p1 ∨ ((p1 ∧ ((p1 ∧ (p2 ∧ p3)) ∨ p5)) ∧ p3))) ∧ p2) → False) ∨ p2))) ∨ (((p3 ∧ p1) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258789612512944289611976467176 : ((True → False) → ((p5 → (((False ∨ p4) → (False ∨ p1)) ∨ p4)) → ((p3 ∨ p1) ∧ ((True ∧ ((((p2 ∨ True) → False) ∨ p2) → p4)) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h12
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190372255154790975646536235675 : ((((p5 ∨ p5) ∨ (((p4 ∧ p2) ∧ True) ∧ p2)) ∨ True) ∨ (((p1 ∨ p3) → (p2 ∨ p2)) ∧ (((p2 ∨ (p4 → p1)) ∨ p3) → (p4 ∧ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712700943981498080447338228008 : (((((p2 → p1) ∧ ((p4 ∨ p1) → p5)) ∨ (((((p4 ∨ True) → ((p3 → ((p4 → (p2 ∨ p2)) ∨ p3)) ∨ p3)) ∨ False) ∨ p1) ∨ p3)) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304612229297333706077176741541 : (p1 ∨ ((((p4 → (True → ((p5 ∧ True) ∨ (True ∧ True)))) ∨ False) ∧ ((True → p4) → (((p5 ∨ p5) → True) ∧ (p1 ∨ p4)))) ∧ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231731506468559674484387375502 : (((p2 ∧ p4) → p1) → (((True ∨ ((p2 ∨ p5) ∧ ((((p5 → (p5 → False)) → False) ∨ True) ∨ p2))) → (False ∨ (True → False))) ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138856839998860398934317295229 : (((False ∨ (p2 ∨ (p4 ∨ ((p1 ∨ ((True ∧ (p4 → (p2 → (p4 ∨ (True → p4))))) → p1)) ∧ (p4 ∨ p3))))) ∧ p1) → (p2 ∨ (p3 ∨ p4))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
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
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h13
          case inr h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h14
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h16
          case inr h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178793508717729061802238325268 : ((((True → p4) ∧ p2) ∨ (((True → p4) ∨ p2) → ((p1 → p1) → False))) ∨ ((False → ((True ∨ p1) ∨ ((p3 ∧ (True → p4)) ∨ p1))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118794589010087106997151088044 : ((p5 ∨ (p4 → (p3 ∧ ((p5 → ((p2 ∨ True) ∧ p2)) ∧ (p1 ∧ (p1 → ((p5 ∨ (p5 → True)) ∧ (p2 ∨ (p5 → p5))))))))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304103957456039553459127170216 : (p1 ∨ ((p1 → (((((p3 ∧ (p5 → p1)) ∨ p5) ∧ p3) ∧ (p2 ∧ p4)) ∨ (((p5 ∧ True) ∨ p1) ∨ ((p3 ∧ p2) ∧ (p2 ∨ p4))))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776137562169607126582715045340 : (((p1 ∨ ((((p1 ∧ ((p4 ∧ ((((p5 → p4) → p5) ∧ (((p3 ∨ (p5 → p5)) ∧ False) ∧ p3)) ∧ p2)) → p2)) → p5) ∨ False) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234015343116657784426931503056 : ((p5 ∨ (p4 ∨ p2)) → (((((p3 ∨ ((True ∨ p3) ∨ p2)) ∧ ((p3 → p2) ∨ ((p5 ∧ p3) ∧ p5))) ∨ True) ∨ p3) ∨ ((p5 ∧ p2) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1520936442293229700458228947 : ((((p1 → p4) ∧ ((p5 ∧ p4) → p3)) → (((False ∨ (p3 ∧ p3)) → ((p1 ∧ (p5 → p3)) → (p3 ∧ p4))) ∧ p4)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212427744838604716405750234576 : ((p3 ∨ ((p4 → p4) ∨ False)) ∧ ((False ∨ p4) ∨ (p5 → ((p3 ∧ (p1 → p5)) → (((p1 → (p4 ∨ p2)) → p2) ∨ (True ∧ (p1 → p1))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135144392045103193463809790468 : (((p4 ∨ ((False ∧ ((((p3 ∨ (p3 → (p1 ∧ (False → (p4 ∧ p2))))) ∧ p1) ∧ True) ∨ True)) ∧ p1)) ∨ (p2 ∧ p5)) ∨ (p1 → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147060648380418775273038882450 : (((((False ∧ (p1 ∧ (p4 ∨ p2))) ∧ (False ∧ True)) ∧ ((p4 ∨ ((p3 ∨ p2) ∧ False)) → (p4 → p1))) ∧ p4) ∨ (p2 ∨ ((False ∨ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156824004599517327696734629322 : (((p4 ∨ (p1 → (((p4 ∧ p1) ∨ (((p5 ∨ p4) ∨ False) ∧ (p4 → (p5 → p1)))) ∧ p5))) ∧ False) ∨ (p5 ∨ (((False ∧ p2) ∧ True) → p5))) := by
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118558926918415352171790055640 : ((p3 ∨ (p5 → (((p3 ∨ (((p5 → True) ∧ (((((p5 ∧ (True → p3)) ∧ p5) ∨ True) ∧ p1) ∨ p2)) ∨ False)) ∧ False) ∨ p5))) ∨ (p2 → p4)) := by
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
theorem thm_5_vars_326220708315426884285229257571 : (p5 ∨ (p3 → (((((p3 ∧ (True ∧ p1)) → p2) ∧ (p4 → p2)) → (((p1 ∨ False) ∧ ((((True ∨ True) → p2) ∧ False) → p4)) ∨ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115373802960423221092723268280 : ((((((p5 ∧ p5) ∧ p4) ∨ p2) ∨ (p3 ∨ True)) ∧ ((p5 → ((p3 ∧ ((p1 ∨ p3) ∧ p3)) ∧ (p4 ∨ True))) ∨ (p3 ∧ p2))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735340156132874252884637117460 : ((((p4 ∨ False) ∧ (p1 ∧ ((p5 ∧ (((p2 ∨ p5) ∨ (p1 ∨ p2)) → (p1 ∧ ((p4 ∨ (p2 ∧ (False ∨ p2))) ∨ p4)))) ∨ (p1 ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_560059152256629795621954408117 : (((p4 ∨ (((((p1 → p1) → (p5 ∧ True)) ∧ True) → p5) ∧ ((True ∧ (p3 ∧ (p1 ∧ ((p5 → True) ∧ (p3 ∨ True))))) ∨ (False ∨ True)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42172587948834932378583309446 : (((True ∧ (((((p4 ∧ True) → p1) ∧ (p2 ∨ (p4 ∧ (True ∧ p4)))) ∧ (p3 → ((((True ∧ p5) → p3) ∨ True) ∨ p3))) ∧ False)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349068279198122087931016169683 : (p3 → (p5 ∨ (True ∧ (True → ((p2 ∧ ((False ∨ p2) ∧ (((p4 ∨ (((p2 ∧ p4) → (p3 → False)) → p4)) ∧ (p4 ∧ False)) ∨ p2))) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329169336948286214021123469372 : (True → (((p3 ∨ p5) → (True ∨ p2)) → ((True ∨ ((p5 ∨ p4) ∧ (True ∨ (False ∨ ((p1 → p4) ∨ ((p1 ∧ p2) → True)))))) → (False ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
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
theorem thm_5_vars_611883561169156354329449276183 : (((((p5 → ((p3 ∨ ((False ∨ p2) → ((((p3 ∧ p5) ∧ p4) ∨ p4) ∧ (p1 ∨ ((False ∧ p3) → p3))))) ∧ (False → p5))) → p5) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_42161650299101873644257050023 : ((((p3 → p2) → (((p4 ∨ (p5 ∨ False)) ∨ ((p4 → p1) → p2)) ∧ ((((True ∧ (p1 → p1)) ∨ True) ∧ p5) ∧ (p5 → True)))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351868133462084341246043416375 : (p4 → ((((((False ∨ p5) ∨ (False ∨ True)) ∧ p4) ∧ p4) ∨ p5) ∧ ((False → (True ∨ (p4 ∧ p3))) ∧ (((p1 ∨ (False ∨ p5)) ∧ p1) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234202581085821109249213871736 : ((False → (p2 ∧ p4)) → (((False ∧ p3) → (((p5 ∨ p4) ∨ (p3 ∨ p1)) ∧ (p2 ∨ (True → p1)))) → ((p2 ∨ True) ∨ ((False → p4) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113304357954417390721142590207 : ((((((False ∨ False) → True) ∧ p1) ∧ ((((((p5 ∧ (p3 ∧ True)) → (True ∨ True)) → p3) → p1) → p3) ∨ True)) ∧ (p4 → True)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118584820856446868153424174820 : ((p4 ∨ ((((((p3 ∧ (p2 ∧ ((False ∧ p2) ∨ p1))) → ((False → (False ∧ p4)) ∨ False)) → True) → (False ∧ p1)) → p3) → p5)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53681630078792764095029160150 : (((False ∧ ((p1 ∧ (p3 → p2)) ∧ ((p2 → p5) ∧ p4))) ∧ (((((False → p4) ∧ p5) ∧ False) ∨ ((False → p1) ∨ p4)) ∧ (p5 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197788438366672827241932180418 : ((((p4 ∧ p5) ∧ p3) ∨ ((p1 ∨ p4) → p5)) ∨ (((p4 ∨ ((p4 ∨ p4) ∧ (True → p4))) ∧ ((((p3 → True) ∨ p5) ∧ True) → True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343036789915025334953848460587 : (p2 → (((True ∧ p2) → (p5 ∨ p4)) → ((p5 ∧ ((p1 ∨ (p5 ∧ (p4 → p3))) ∨ ((True ∧ ((True ∨ p4) ∧ p5)) ∨ p1))) ∨ (False → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113111595547495617346467472188 : (((False → ((((((p1 ∧ p5) → ((p2 → False) ∧ False)) ∨ (((True ∨ (p1 → p1)) ∧ p5) → p1)) ∧ p2) ∧ True) → p5)) → p4) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307758833111812753126273828000 : (p1 ∨ (p3 → ((p2 ∨ (p2 → True)) → (((True → (True ∧ p1)) ∨ p3) ∨ (((p2 ∨ True) ∨ (((p1 ∧ p1) ∨ p1) → p5)) ∨ (True → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179232199643119254162087718639 : ((p4 ∧ (p2 → (p4 ∨ ((((p1 ∧ p5) ∨ False) → p3) ∨ (p4 ∨ p1))))) ∨ (((p3 → p5) ∨ (False → (p4 ∧ (p2 → (p2 ∧ False))))) ∨ p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184010080420396975332684747280 : (((((p3 ∨ ((False → True) ∨ p2)) → (False ∧ p5)) ∨ p5) ∨ p3) ∨ ((p4 ∨ p5) ∨ (True ∧ (((True → p5) → (False ∨ p4)) → (True ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37979344630213728436472687390 : ((((((((p1 ∧ True) ∧ (True → (False ∧ p4))) → ((p3 ∧ p1) ∧ p1)) → (False ∧ p1)) ∨ (p5 → (False → p5))) ∨ (p4 ∧ True)) ∧ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_306470811943998560152009256289 : (p1 ∨ ((True → False) ∨ (p1 ∨ ((((p5 ∧ False) ∨ (p4 ∧ False)) ∨ (p5 ∨ (p4 ∨ ((p3 → (p3 ∧ p3)) ∧ (p5 → True))))) ∨ (p4 ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158088247687878214855316250323 : (((p4 ∨ (((True ∨ p5) ∨ p2) ∧ p1)) → (p4 → (((p3 → p1) ∨ p5) ∧ ((False → True) → False)))) ∨ ((p2 ∧ ((p1 ∧ False) ∧ p3)) → p2)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700888056902463977759968905856 : ((((((p5 ∨ (((p2 ∨ False) → p3) → p1)) ∨ False) ∨ p2) ∧ (p3 ∧ (p5 ∧ ((p2 ∧ (True ∧ (False ∧ p2))) ∨ ((False → True) → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664976693266210190453306966751 : ((((p3 → (p2 → (p2 ∧ (False ∨ ((p5 ∨ ((True → (False ∨ ((p2 ∧ p3) ∨ p4))) ∨ (False ∨ p4))) ∨ (p1 → p1)))))) → (p5 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54886908701811460381162720126 : ((((((p3 → p2) → p1) → p1) ∨ p5) ∧ (((p2 → p4) ∧ p4) ∨ ((False ∨ ((p2 ∨ ((p5 ∧ (False ∧ p2)) ∧ p2)) → p5)) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680446559030625712028249966308 : ((((((True ∨ ((p4 → p5) ∧ (False ∨ ((p2 → False) ∧ p3)))) ∧ p5) → (False → ((p5 → p5) ∧ p5))) → (p5 ∨ (p5 ∨ (p2 ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234449206035722373441476767654 : ((p2 → (p4 ∧ p3)) → (((p3 ∧ (p1 ∧ (p1 ∧ ((p2 ∧ False) ∧ p4)))) ∧ (p3 → p1)) ∨ (True ∨ ((True ∨ p3) ∧ (True → (p3 ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



