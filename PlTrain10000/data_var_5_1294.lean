variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345476057001873024627333920256 : (p3 → (((((((p5 → p4) ∨ ((False ∨ p1) ∨ (p1 ∨ p2))) ∧ p2) → (((p1 ∧ p5) → p5) → False)) ∨ p4) → (False ∧ (p1 ∨ False))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114963023842844268269250757048 : (((p5 ∨ ((((((p3 ∨ False) ∧ (p3 ∧ p4)) → p4) ∧ True) ∨ p3) → p4)) → (p5 → ((True ∧ False) ∨ ((True → True) → p1)))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59098868536600276715506842101 : (((p5 ∧ p5) ∨ ((p1 ∧ ((((p1 ∧ (((p5 ∨ p2) → (p3 ∧ p3)) → False)) ∨ p5) → (False ∨ p1)) → p1)) ∨ ((p2 → True) ∨ False))) ∨ False) := by
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
theorem thm_5_vars_786098879878511528720385088 : (((p5 ∧ p2) → (p3 → ((p1 ∨ (p4 ∧ ((False → p2) → (((True → p2) → False) ∨ False)))) ∨ ((p1 → p2) ∧ (p3 ∨ False))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301051403803716974303247706081 : (False ∨ (((((p3 ∨ p5) ∨ p3) ∨ (False → p1)) ∧ (p2 ∨ p4)) ∨ ((False ∨ ((p4 ∨ ((False → True) → p5)) ∧ (p3 ∨ (p2 → p3)))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47254640954013406802688065532 : (((((p4 → p1) ∨ ((p5 ∨ p2) ∧ True)) ∨ ((True ∧ ((p2 ∨ False) ∨ p1)) → ((p2 ∧ False) ∧ ((p5 → p4) → False)))) ∨ (False ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157514886250266500156211504872 : (((False ∨ (p4 ∧ ((p3 ∧ ((True ∨ False) ∧ ((p3 ∨ p1) ∨ p2))) ∧ (p1 ∨ p2)))) ∨ (False ∨ p4)) ∨ ((False ∧ ((p1 ∧ False) → p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251313676260599419228451656656 : ((p2 → p3) ∨ (((p2 ∧ (((p3 → p2) → (p3 → (p1 ∧ p2))) → (p1 → (p3 ∧ p5)))) → p1) ∨ ((p5 → (True → (True ∨ p5))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257636923106986283650202638075 : ((p3 ∨ p2) → ((((p2 → (p3 ∧ p4)) ∨ p5) → False) → ((((p3 ∧ (p4 → p2)) ∧ (p3 → p5)) ∧ (p1 ∨ (p1 ∨ p2))) → (p4 ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h12 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h13 := h7 h12
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h14 : ((p2 → (p3 ∧ p4)) ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h15 := h2 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h17 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h18 := h7 h17
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h19 : ((p2 → (p3 ∧ p4)) ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h20 := h2 h19
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h23 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h24 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h23
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h25 := h7 h24
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h26 : ((p2 → (p3 ∧ p4)) ∨ p5) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h25
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h27 := h2 h26
        -- False on the left can always be used.
        apply False.elim h27
      case inr h28 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h29 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h8
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h30 := h7 h29
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h31 : ((p2 → (p3 ∧ p4)) ∨ p5) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h30
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h32 := h2 h31
        -- False on the left can always be used.
        apply False.elim h32
    case inr h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h34 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h35 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h34
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h36 := h7 h35
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h37 : ((p2 → (p3 ∧ p4)) ∨ p5) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h36
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h38 := h2 h37
        -- False on the left can always be used.
        apply False.elim h38
      case inr h39 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h40 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h8
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h41 := h7 h40
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h42 : ((p2 → (p3 ∧ p4)) ∨ p5) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h41
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h43 := h2 h42
        -- False on the left can always be used.
        apply False.elim h43
  -- Conjunctions on the left can always be decomposed.
  let h44 := h3.left
  let h45 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h46 := h44.left
  let h47 := h44.right
  -- Conjunctions on the left can always be decomposed.
  let h48 := h46.left
  let h49 := h46.right
  -- Disjunctions on the left can always be decomposed.
  cases h45
  case inl h50 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h51 =>
      -- One of the premise coincides with the conclusion.
      exact h51
    case inr h52 =>
      -- One of the premise coincides with the conclusion.
      exact h48
  case inr h53 =>
    -- Disjunctions on the left can always be decomposed.
    cases h53
    case inl h54 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h55 =>
        -- One of the premise coincides with the conclusion.
        exact h55
      case inr h56 =>
        -- One of the premise coincides with the conclusion.
        exact h48
    case inr h57 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h58 =>
        -- One of the premise coincides with the conclusion.
        exact h58
      case inr h59 =>
        -- One of the premise coincides with the conclusion.
        exact h48



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171429080570881145959587134690 : ((((False ∨ p4) ∨ ((((False ∧ p4) ∨ False) ∨ (p5 ∨ p2)) → (p4 ∧ p3))) ∧ p1) ∨ (((p1 ∨ p1) ∨ True) ∨ (True ∨ (p1 → (p2 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208980553010140109490275446823 : ((True ∨ (p4 ∨ ((False ∧ False) ∧ False))) → (((((False ∨ (p4 ∧ p1)) ∧ ((p2 → p4) ∨ True)) ∧ p2) ∨ True) ∨ (False ∨ ((p2 → p1) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- False on the left can always be used.
      apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244584469261053883330904751086 : ((False ∧ p4) ∨ (((p1 ∨ p3) → p1) → (((((p4 ∧ p1) → (p1 → p4)) ∨ p1) ∧ True) → (p2 → ((((p4 ∧ True) ∨ p4) ∨ p2) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792165991579839166531133107845 : (((True → ((p1 ∨ (((((True ∧ False) ∨ p5) ∧ p4) ∨ (p3 → p3)) ∧ (p1 → (((True ∨ p3) ∧ p2) ∨ p2)))) → (p2 ∨ (p2 → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38096926958860137200036375297 : ((((True → (((((p1 ∨ (p5 ∨ False)) → (True → (p2 → ((p3 → p4) ∨ p4)))) ∨ False) ∧ (p4 → p5)) → True)) → (True → p1)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148091682474514936924790075164 : (((((True ∧ (p1 → (True ∨ True))) ∧ ((False ∨ ((p2 → p2) ∨ p1)) → (p2 ∨ p4))) → True) → (p1 ∨ False)) ∨ (p4 ∨ ((p1 ∨ True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56608928019577544505164186976 : (((p5 → (p2 ∧ (p4 ∨ p4))) → (((((True ∨ (False → (p5 ∧ ((True ∨ (p5 ∧ (True → p2))) → p1)))) → p3) ∧ p5) ∨ True) ∨ p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225911703572442817579312380789 : (((p1 ∧ p5) ∨ p1) ∨ (((((False → p2) ∨ (p4 → (p2 ∧ (False → p3)))) → p2) ∨ p4) ∨ (p5 ∨ ((p3 → (p3 ∨ p5)) ∨ (p4 → False))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199281062430568104087266084969 : ((((False ∧ (p5 ∨ (p5 → p2))) ∧ False) ∨ p2) → ((False ∨ p1) ∨ (((p4 ∧ ((p2 → ((True ∧ p4) ∨ p1)) → p5)) ∨ (p1 → p2)) ∨ True))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158580767598251217272773098952 : ((True ∧ (True ∧ (True → (((p2 → p4) ∨ (((False ∧ False) ∨ p2) ∨ False)) → ((p3 → p3) ∧ p3))))) ∨ (p3 → ((p2 ∨ p3) ∨ (True ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158928927050978317226599076031 : ((p2 ∨ ((((True → p4) ∧ ((((True → False) → p5) → p4) ∨ p5)) ∧ (True ∧ (p4 ∨ p5))) ∧ p1)) ∨ (p3 ∨ (p3 ∨ ((p1 → True) ∨ False)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178079128010389330503588637294 : ((((((((p3 ∨ True) ∧ p1) ∨ p3) ∧ (False → False)) ∨ p3) → p4) → p2) ∨ ((True ∧ (p3 ∨ p5)) → (((p3 ∧ p4) ∧ p2) → (p2 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119573814831792770944242260513 : ((p5 → ((p2 ∨ ((p1 ∨ p2) → False)) ∨ (p1 ∨ (((p1 → p1) ∨ ((p3 ∧ p3) ∧ (p4 ∨ ((p4 ∧ p5) ∨ p3)))) → p3)))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173338330556507861111319814584 : ((p2 → (p5 ∧ (((True ∨ (p5 → p4)) → p5) ∨ (p2 ∧ (False ∨ (p1 ∨ p3)))))) ∨ ((p1 ∨ True) ∨ (((p5 ∨ p4) ∧ False) → (p5 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198684008776874018620889907373 : ((p4 ∨ ((p2 ∧ p1) ∨ ((True → p1) ∧ p2))) ∨ (((p2 ∧ True) ∨ (((True → (p5 → p1)) → (p1 → True)) ∨ (p1 → (p2 → p3)))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259009182513435640501374664006 : ((True → p4) → (((p4 → p1) → (((p5 ∧ p1) → ((False → (p3 → (p2 ∧ True))) → ((p1 ∨ (True ∧ (p1 ∨ p2))) ∧ p4))) → p4)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338246881482862588228734198245 : (p1 → ((p2 ∧ (False ∧ ((p4 ∧ p2) ∧ p1))) ∨ (((p5 ∨ ((False ∧ (((p2 → p3) ∧ p2) ∧ p5)) → (p4 ∧ p3))) → False) → (p1 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p5 ∨ ((False ∧ (((p2 → p3) ∧ p2) ∧ p5)) → (p4 ∧ p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
    -- Conjunctions on the left can always be decomposed.
    let h7 := h4.left
    let h8 := h4.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h3
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63022033370481698129205782123 : ((p4 ∧ (p4 → ((p4 ∧ (((p2 → (p3 → False)) ∨ ((True → False) ∨ p5)) ∧ p2)) ∧ ((False ∨ ((True ∨ (p5 ∧ p3)) ∧ p2)) → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191269867115465242041405861179 : (((False ∨ p2) ∧ (p5 ∧ ((p3 ∨ (p3 ∨ p5)) → p2))) ∨ (((True ∨ (p2 → (((p3 ∨ (False ∧ True)) ∧ p2) ∧ (True → p1)))) ∨ p5) ∨ p2)) := by
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
theorem thm_5_vars_114024150492030145056117633860 : ((((p3 ∨ (p2 ∨ (p1 ∧ (((p4 ∨ False) → ((False ∨ p1) ∧ (p5 ∧ p1))) ∧ (True → False))))) ∨ p4) ∨ (p1 ∧ (p4 ∧ False))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168963479370418594681533904887 : ((False → (((p5 ∧ (p1 → p3)) ∨ ((True ∧ False) ∧ (True → ((p4 ∧ p5) → p5)))) → p5)) → ((p4 ∧ (p2 → False)) ∨ (False → (p2 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673133157369643631185870399341 : ((((((p2 ∧ ((p1 → p2) ∧ p1)) ∨ (p1 → (p4 ∨ (True → p1)))) → (p2 → (p3 → (p2 ∨ (p3 ∧ p1))))) → ((p3 ∨ p3) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61547805595327720868627055992 : ((p1 ∧ ((True ∧ (((((p4 → p1) → p3) ∧ False) → p3) ∧ p5)) ∨ (((False → False) → (p1 ∧ (p4 → p5))) ∧ ((True ∧ True) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258542150896771787139582806961 : ((p5 ∨ p3) → (((False ∨ p3) ∨ ((p3 ∨ p1) ∨ (p5 ∨ (False ∧ (p2 ∧ (p1 ∧ p1)))))) ∨ (False ∨ (p2 → ((p4 → (True → p2)) ∧ p5))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38645917370174844677579833663 : (((((p3 ∨ (p5 ∧ ((p4 ∧ p4) ∧ p1))) ∨ p5) → ((((p3 ∨ False) ∨ False) ∨ (p3 ∨ (((False ∨ p3) ∨ p1) ∧ True))) ∨ p2)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617830364578433129062689560223 : ((((((p2 ∨ ((p3 → True) ∧ p4)) ∨ p2) → ((p2 ∨ ((p1 ∧ (p1 ∨ p4)) ∧ (False ∧ (p1 ∨ True)))) → ((False ∨ p5) ∨ p1))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261980500298891777574664090948 : (True ∧ ((True ∧ ((p2 ∨ ((p5 ∨ (p1 ∨ (((((((p4 ∧ p1) → False) → True) ∨ p3) → p1) → p3) ∨ True))) ∨ False)) ∨ (True → p3))) ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57083648559478973316656584115 : ((((p1 ∧ p2) ∧ p3) ∨ ((((((p5 → ((p5 → ((False → p2) → (p1 ∧ p3))) ∧ p2)) ∨ True) → p2) ∨ False) → p2) ∨ (False ∨ p2))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : ((p5 → ((p5 → ((False → p2) → (p1 ∧ p3))) ∧ p2)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49892583184590811915724476493 : (((((p5 ∧ p5) ∧ (((p2 ∨ (((p4 → p5) ∨ p2) → (p2 → False))) ∨ p2) ∨ (p4 → p1))) ∨ True) ∧ (p2 → (p1 ∨ (p2 ∨ p1)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62238033908498255095938677062 : ((p3 ∧ (((p3 → (((True ∧ p1) → (p4 ∧ p2)) → ((False ∨ (p5 → p5)) ∧ p3))) → (((p5 ∨ (False ∧ p4)) → p1) → p2)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604393223905272377933040836705 : ((((True → (p1 ∧ ((True → (((((True ∧ p1) ∧ (((p1 → p3) ∧ True) ∧ True)) ∨ (p5 ∨ (True → p3))) ∨ p2) ∧ p4)) → p2))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339757792944386691336580645491 : (p1 → (p4 ∨ ((p1 ∧ p5) ∨ ((True ∧ (((False → p4) ∨ p5) ∧ ((p2 ∧ (True → False)) ∧ (False ∨ (p3 → ((p5 ∨ p3) ∨ True)))))) → p5)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h15 := h11 h14
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h6.left
    let h18 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h21 =>
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136346208584614239610787935761 : (((p3 ∨ (False ∧ (p2 ∨ p4))) ∧ (p4 → ((p3 ∨ p5) ∧ ((p3 ∧ p2) ∧ ((p1 ∧ False) → (p3 ∧ (False ∨ p5))))))) ∨ ((True ∧ False) → p3)) := by
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
theorem thm_5_vars_147476656764671169574611588459 : (((p2 ∧ ((p1 ∧ (p1 ∨ ((((p5 → p1) ∧ True) ∧ False) → (True ∧ True)))) ∨ ((p2 → p3) ∧ False))) ∨ False) ∨ (((True ∧ False) ∧ p2) → p3)) := by
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
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53146446908445882597701520579 : ((((((p5 ∧ True) ∧ (((p4 → p4) ∧ p1) ∧ p2)) ∧ p1) ∨ p4) ∨ ((p5 ∨ ((p3 → p1) ∧ (False ∨ (p2 → (p5 → p4))))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_836700507579132151432933882398 : ((((((((p2 → (p4 ∧ ((p1 ∨ (False ∨ p5)) → ((((p5 → p3) ∧ (p1 → True)) ∨ False) → p4)))) ∧ p2) ∨ True) ∨ False) → p4) ∨ p4) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : ((((p2 → (p4 ∧ ((p1 ∨ (False ∨ p5)) → ((((p5 → p3) ∧ (p1 → True)) ∨ False) → p4)))) ∧ p2) ∨ True) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
theorem thm_5_vars_150295316252772472905702949519 : ((p4 → (((((p2 → (False → (p1 ∨ p3))) ∨ (((p5 ∨ p3) ∧ p2) ∧ p5)) ∧ True) → p2) → (p5 ∨ p1))) ∨ (p5 → (True → (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246652739569695541064337838602 : ((p5 ∧ p3) ∨ ((p3 → False) ∨ ((p4 → (((p1 ∨ (True ∧ False)) ∧ (p4 ∨ ((True → (p2 ∧ (p4 → (False ∧ p4)))) ∧ p4))) ∨ True)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_706470733071223033394736502163 : ((((p3 ∨ (True → ((p3 ∧ p2) ∧ (p5 ∨ p2)))) ∧ ((((p4 → p5) → (p5 → p4)) ∨ p1) ∨ (True → (((p1 → True) → p1) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119273603759706942281188522930 : ((p3 → (((False ∨ ((True → (False ∨ (p2 → p2))) → (p2 ∨ (True → (p2 ∨ p5))))) ∨ (False → (True → (p3 → p4)))) ∧ p1)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262179480778186893436405577554 : (True ∧ (((((((((p1 ∨ (False → (True ∧ (False ∧ (True ∧ p1))))) ∧ (True ∨ (p4 ∧ False))) → p3) ∧ p4) ∧ p5) ∨ p3) ∨ True) → p1) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43140624166962512828438415328 : (((((p5 → ((p4 ∨ (False ∨ (p2 ∧ False))) ∧ p3)) ∧ ((p2 ∧ (p4 → True)) → (((p4 ∧ p4) ∨ p3) → (p4 ∧ p4)))) ∧ p2) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256273681844972555521596834786 : ((False ∨ p1) → ((((p1 ∧ (p2 ∧ p4)) ∨ (((p5 ∨ (p1 ∧ (p2 ∨ (False ∧ False)))) ∧ p3) → (p4 ∧ (p5 ∧ (p3 ∧ p2))))) → p3) ∨ True)) := by
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
theorem thm_5_vars_62201117393764863681945420895 : ((p3 ∧ (((p3 ∧ (p4 ∨ (p1 → (p3 ∨ (p1 ∧ p4))))) ∨ ((((p3 → p3) ∨ (p4 ∨ p3)) ∨ ((p1 ∧ False) ∨ False)) ∧ False)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135109024613308285290989237587 : ((((p1 ∧ (p5 ∧ p1)) ∨ (((p5 ∨ (False ∧ p3)) ∨ ((True → p4) ∨ p3)) ∨ ((p3 ∨ p4) ∧ p2))) ∨ (p2 → p3)) ∨ ((p1 ∧ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317997292680289644581647756261 : (p4 ∨ ((p5 → (p5 ∧ ((p3 ∨ ((((True ∧ False) ∨ (p3 → False)) → (p3 ∧ (True ∧ p3))) → ((p3 → p5) → (p2 ∧ p3)))) ∧ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178253841895028924331183030751 : ((((((p5 ∨ (False ∧ (p5 ∨ True))) ∧ False) → True) → p4) ∧ (p2 ∨ p1)) ∨ (p1 → (p2 ∨ (((((True → p3) ∧ p4) → p2) ∧ p4) ∨ p1)))) := by
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
theorem thm_5_vars_4069512183340692888575211057 : (p2 ∨ (p3 ∨ (((((((p3 ∧ (p4 ∧ (p5 ∨ p5))) → (True ∧ False)) ∧ p3) ∧ p2) → (p1 ∧ (p4 ∧ p5))) → p3) ∨ (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153702132556886019790966708056 : ((p2 → (p2 → (p3 ∨ (((((p2 ∨ p2) ∧ (((p3 → (False ∧ p2)) ∨ p4) ∧ p2)) ∨ False) → False) → False)))) → ((p3 → False) ∨ (True ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246119351807090738559237979177 : ((p4 ∧ p1) ∨ (True → ((p1 → ((((p3 ∧ p5) → p3) ∧ p1) ∧ (p5 ∨ (p3 ∨ ((False ∧ (True ∨ p4)) ∧ (p2 ∨ (p4 ∨ p2))))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_510124705186874237064747588362 : ((((p2 → True) ∧ (((((False → (False ∧ ((p2 ∨ (False ∨ (p4 ∧ False))) ∧ p4))) → (p1 → p1)) ∧ p3) → (p4 ∨ (p2 → p1))) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40063413103383901826155236938 : (((((((False → p1) ∧ p3) → ((p2 → (False ∨ ((((p3 ∧ p5) ∨ p5) ∧ (True ∨ p1)) ∧ p1))) → (p4 ∧ True))) ∨ p2) ∧ p4) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147860479930223892052872669147 : (((p1 → (((p3 → p5) → (((False ∨ p2) ∧ ((False ∨ (p5 ∧ (p4 ∧ p4))) ∨ p2)) ∧ False)) ∨ True)) → p3) ∨ ((p2 ∧ (p4 → False)) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206028214816608301567494348808 : ((p2 ∧ ((p3 ∨ p4) ∧ (p5 → p4))) ∨ (p5 → (p5 → (p1 → (p1 ∧ (((p2 ∨ ((p2 ∨ p1) ∨ p5)) ∨ (p1 ∨ p4)) ∨ (True ∧ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46212829356573589586029175288 : ((((((p4 ∧ ((True → (p5 ∧ p4)) ∨ p2)) ∧ (p5 ∨ (p1 → (p1 ∧ p1)))) ∧ ((p5 → True) ∨ p4)) ∧ (p2 → p5)) ∧ (False ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299292501615440663741225310363 : (False ∨ ((((p2 ∨ p4) ∧ (((p1 ∧ p5) ∧ (p2 → p4)) → (p3 ∨ p5))) → ((((p1 ∧ p3) ∧ (p2 → (False → True))) ∨ p4) ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631267038500509784798220641237 : (((((((p4 → ((p2 ∧ False) ∧ p2)) ∨ ((p4 → (((p2 ∨ (p1 ∧ p2)) → True) ∧ (False → True))) → (p5 ∨ False))) → p5) → p2) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338764088334587386662284430274 : (p1 → ((p1 ∧ False) ∨ (((((p4 ∨ p2) ∨ False) ∨ (p3 → (((False ∧ p4) → (p1 ∨ (p1 ∧ (p5 ∧ False)))) → p3))) → (True → False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704815749426010716896657496339 : ((((True ∨ (p5 ∧ (p3 → ((p3 → (p3 ∧ p1)) → p4)))) → ((((True ∨ p3) → (p5 → p1)) ∨ p3) ∨ ((p3 → (p3 ∨ p3)) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_563508909071373686013969273849 : (((p5 ∨ ((p1 ∨ p2) ∨ (p4 → ((True ∨ (True ∧ ((p1 → (p3 ∨ p2)) ∨ (p1 ∨ p1)))) ∧ ((False ∧ (p3 → p5)) ∨ (p3 → p4)))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314569918789907357350819504448 : (p3 ∨ ((((((True ∨ True) ∨ p3) → False) ∧ (p5 ∧ (p5 ∨ (p1 ∧ (p4 ∨ (p5 → p1)))))) ∧ True) → ((((p2 ∧ False) → p4) → p3) ∨ p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : ((True ∨ True) ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h15 : ((True ∨ True) ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h16 := h4 h15
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h18 : ((True ∨ True) ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h19 := h4 h18
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68600327043928584364031334839 : ((p4 → ((((False ∧ ((p4 → (p4 → (p3 → p4))) → (p2 ∧ (False ∧ ((True ∨ False) ∧ (p4 ∧ (p3 → True))))))) ∧ p1) ∨ p4) ∨ p5)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197285700383611966859667930016 : ((((p3 → (p1 ∧ p2)) ∨ (p2 ∨ p1)) → p3) ∨ ((False → ((p3 → ((((p1 ∨ p1) ∧ p4) → p4) ∧ (True ∧ p2))) → (True ∨ p1))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167862241833722438874142185796 : ((((p5 ∨ ((p5 ∨ (p4 ∧ (p4 → False))) ∨ p4)) ∧ p5) → (((True ∨ p1) ∧ p3) → False)) → ((((p4 → True) ∧ (p3 → p4)) ∨ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773378713830948403612424189311 : (((False ∨ ((p5 ∨ (p2 ∨ ((((p2 → (p5 → p2)) → ((False ∨ (((p2 → p4) ∧ p5) → (True → p4))) ∧ p3)) ∧ p4) ∧ p2))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51108876827617340937451245312 : ((((p3 → (False ∧ (((False ∨ ((p2 ∧ False) ∨ p5)) → ((p1 ∨ p1) ∧ False)) ∧ p5))) ∧ p4) ∨ ((False ∧ (p4 ∧ (p2 ∧ p5))) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190348059287168323566995435729 : ((((p1 ∨ (p4 ∧ p1)) ∨ (True → (False ∧ p4))) ∨ True) ∨ (p5 ∧ (p1 ∨ (True ∨ (((False → (True ∨ ((p2 ∨ p1) ∧ p2))) ∧ p5) ∨ p3))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_386829537086370110349170284129 : ((((((p5 ∧ p2) → ((((((p3 ∨ (p1 → False)) → False) ∧ (((True → p4) ∨ p4) ∨ p1)) ∧ p1) ∧ p3) → False)) → (p1 ∧ p3)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_178832368557601835306308297661 : ((((p2 ∨ p5) ∧ p1) → ((True ∧ ((p4 ∨ p2) ∨ (p3 → p4))) ∨ p2)) ∨ (p3 ∨ (p5 → (True ∨ ((p4 ∨ (p4 → (p3 ∨ False))) → False))))) := by
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
theorem thm_5_vars_135073017748394766518885710723 : ((((True ∧ ((((p1 → p4) ∧ p3) ∨ (True ∧ (True ∧ p4))) ∧ ((p4 ∨ p4) ∨ False))) ∨ (p4 → p5)) ∨ (p1 ∧ False)) ∨ (True → (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180810402973213717949089438490 : ((((False ∧ p4) → p2) ∧ (p3 → (p5 ∧ (p5 → ((p1 ∨ p5) → p5))))) → (p2 ∨ ((False → p2) ∨ (False ∨ (False ∨ ((p2 → False) ∧ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690223665225435519285436328272 : ((((p5 ∨ ((((False ∧ p3) ∧ p1) ∨ ((False ∧ True) ∧ ((p1 ∧ p2) ∧ p3))) ∨ True)) ∨ (((p5 ∨ p2) → (False ∨ p4)) → (p5 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711553161136337900314784753085 : ((((False → (p5 ∨ (p4 ∨ (p4 ∧ p1)))) ∧ (((False → (p4 ∧ (False ∨ p2))) ∧ p5) → (p3 ∧ ((p4 ∧ (p4 ∨ p2)) ∧ (False ∨ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634614102317153403138902909246 : (((((p2 ∨ ((False ∧ True) ∨ ((((True ∨ (p1 → p2)) → (p4 ∧ p3)) → p3) ∧ ((p3 → p4) ∨ True)))) ∧ (p2 ∧ (False ∨ p5))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118621256466956000613543648059 : ((p4 ∨ (((True → (p3 → p1)) ∨ ((True ∨ True) → p5)) ∧ ((p2 ∨ ((((p5 ∨ p3) ∨ True) ∨ (p3 → False)) → False)) ∧ p5))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114762638514320349031543950414 : (((True → ((p1 ∨ (p5 → ((p4 → p4) ∧ ((True ∧ True) ∨ (p4 ∧ p3))))) ∧ p2)) → (p5 ∨ (False ∨ (p4 → (p5 → p3))))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682284039683941947450483520046 : (((((((p4 ∧ False) ∨ p1) → (((False ∧ ((True → p5) → p4)) → False) ∧ p5)) ∧ (p2 ∨ p4)) ∧ (((p4 ∨ True) → (p1 ∨ p3)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257070332892839125774680717500 : ((p2 ∨ False) → (((False ∨ ((p4 ∨ p4) ∧ ((p4 ∧ p4) → False))) ∧ ((p5 ∨ (p1 → (True ∧ p5))) → (p5 → (p2 ∨ (p2 ∧ False))))) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h10 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h11 : (p4 ∧ p4) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h9
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h12 := h8 h11
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h15 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h16 : (p4 ∧ p4) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h14
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h17 := h8 h16
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- False on the left can always be used.
        apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53753961214954626851931347915 : ((((((p4 → True) ∧ True) ∧ (p3 ∧ (p3 ∧ True))) ∧ p4) ∨ ((p3 ∧ p4) ∧ (((p1 ∧ (p2 ∧ p1)) ∧ (p5 ∨ p1)) ∨ (True ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10327960463278130492810725021 : (((p5 ∨ ((p1 ∨ ((((((p3 → p4) ∨ p2) ∨ p3) ∧ (True → ((p5 → (p2 ∨ p3)) → (p5 ∧ True)))) ∨ p3) ∧ p3)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113413145139755365484052840199 : (((((True → (False → (((True ∨ True) → ((((p2 → p1) → p3) → p1) → (p3 → p3))) → p2))) → p1) ∧ p5) ∨ (p1 → p2)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265756492598720585752199023065 : (True ∧ (p4 ∨ ((((p2 ∧ (((p5 → p5) ∧ False) ∧ p4)) ∧ (p5 ∨ p3)) ∧ (False ∧ ((p1 → p2) → (p1 ∨ (p3 ∨ (p5 → p2)))))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53621000925233702236836771673 : ((((p5 ∧ (((p5 → p1) → p2) → p2)) → (p3 ∧ p2)) ∧ (((True ∨ False) → p2) ∨ (((p4 → p5) → ((False ∨ p4) ∧ p4)) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58733809302082292583235124493 : (((p3 → p3) ∧ (((((p2 → True) ∧ (((False → p2) ∨ p4) ∨ p4)) → p4) ∧ False) ∧ (p1 ∧ (p1 → ((p3 ∧ p5) ∧ (False ∨ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4008433341920138294148408839 : (p1 ∨ (p2 ∨ (p3 ∨ (False ∨ (((p4 ∨ p2) → p5) ∨ ((p4 ∨ (p4 → ((p5 → (True ∧ p2)) → p4))) ∨ ((p3 ∧ p5) → p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139012820712852507990681390537 : ((((p1 ∨ (((((p1 ∨ True) → True) → (p3 ∧ False)) ∨ True) ∧ ((False → (True ∧ p2)) → (p2 → p2)))) ∨ p5) ∨ p1) → ((p2 ∧ p4) ∨ True)) := by
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340795151953457737385947928659 : (p2 → ((((p3 ∨ p5) → (((((False ∧ (p5 ∧ (False → p2))) → ((p2 → (p1 ∨ False)) ∧ p1)) ∨ p4) → (p4 ∧ p2)) ∧ p5)) → False) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219603297599885575086931444605 : ((True → (True → (True ∧ False))) → (p3 → ((False ∨ p3) ∧ ((((p2 ∧ True) ∨ p5) ∧ (p1 ∧ ((False → p1) ∨ (p1 ∨ (p1 → p3))))) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h13
  -- False on the left can always be used.
  apply False.elim h13
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h14 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h14
  -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
  have h16 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h15, we can now drive its conclusion.
  let h17 := h15 h16
  -- We need to get the right conjuct of h17 based on <expert-advice>.
  let h18 := h17.right
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225189667185225394243578660174 : (((p4 ∧ p2) ∧ p5) ∨ ((True → (p2 ∧ False)) → ((p3 ∧ p3) ∨ ((p1 → ((False ∧ (p1 ∨ False)) ∨ p3)) → (p2 ∧ ((p2 → p1) → p3)))))) := by
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137341813565014863499723069960 : ((p2 ∧ (p1 → (p5 → ((p5 → (True → (True ∨ ((p4 ∧ p1) ∨ ((p3 ∧ (False ∧ p3)) ∨ (p2 ∨ p5)))))) → False)))) ∨ ((False ∧ p2) → p1)) := by
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
theorem thm_5_vars_118352993070757314701285806903 : ((p2 ∨ (((p4 ∧ (p4 ∧ p2)) ∨ ((p3 → ((p5 → p3) ∧ ((p5 ∨ (p5 → (False → p4))) ∨ False))) ∨ (p4 ∨ p4))) → p1)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



