variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754712224756532005713002340738 : (((False ∧ (p5 ∧ ((False ∨ p4) → (p3 ∧ (((p3 → p5) ∧ (((True → ((((True → p1) ∨ p4) ∨ False) → p1)) ∨ p5) ∨ p4)) ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749069135693588993164805043771 : ((((p5 → True) → ((((False ∨ p4) → False) → (p4 ∨ p3)) ∧ (p3 ∨ ((p2 → (True → (False ∨ (((p4 ∨ p2) ∧ False) → p5)))) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671180623256998182207744468667 : ((((p3 ∨ ((((p3 → p1) ∨ (((p4 ∧ p4) ∧ (p4 → False)) ∨ False)) ∧ ((False → (p1 ∨ p2)) ∨ False)) ∧ False)) ∨ (p1 ∨ (p3 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314834504509530306228055323940 : (p3 ∨ (((p2 → ((p3 ∨ (p3 ∨ p3)) ∧ p2)) ∧ ((p2 → p2) ∨ False)) ∨ (((p5 → p1) ∧ p5) ∨ (((True ∧ (p1 ∧ p3)) ∧ p2) → p2)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720956068668662639992397308489 : (((((p3 ∨ p4) ∧ (p1 ∨ p4)) → (p4 ∧ ((p1 ∧ ((p4 ∨ (p5 ∨ ((False → p3) ∨ (((p4 ∧ False) → False) → p2)))) → p1)) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246685070868107657088384980075 : ((p5 ∧ p4) ∨ ((((False ∧ (p4 ∧ ((p5 → p3) ∧ p3))) → ((p3 ∨ ((p5 ∨ p3) ∨ p3)) → p3)) → ((p5 ∧ (p3 ∨ p1)) ∧ False)) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ (p4 ∧ ((p5 → p3) ∧ p3))) → ((p3 ∨ ((p5 ∨ p3) ∨ p3)) → p3)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h3.left
      let h7 := h3.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h3.left
          let h12 := h3.right
          -- False on the left can always be used.
          apply False.elim h11
        case inr h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h3.left
          let h15 := h3.right
          -- False on the left can always be used.
          apply False.elim h14
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h3.left
        let h18 := h3.right
        -- False on the left can always be used.
        apply False.elim h17
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h19 := h1 h2
  -- We need to get the right conjuct of h19 based on <expert-advice>.
  let h20 := h19.right
  -- False on the left can always be used.
  apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60419355134691681567662174406 : (((p4 → p2) → ((((p1 → (p1 ∨ p3)) ∨ (p2 ∧ (((((True → p4) ∨ False) → (p2 → p4)) → p5) ∧ False))) ∨ (p2 → p5)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700390638408057178083758292050 : ((((p5 ∧ (((p5 → p3) → ((p2 → p3) ∨ (p3 → p4))) → p5)) → (((p1 ∨ (True → p1)) ∨ p5) ∨ (((False ∧ p1) ∨ p3) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303705016284140248990330321819 : (p1 ∨ (((((((False ∨ (p1 ∨ False)) ∧ ((False → p4) ∧ (p1 ∨ p4))) ∨ (((False ∧ False) ∧ (p3 → p5)) ∨ p5)) → False) ∧ p3) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38615623730270025606935965323 : ((((p3 ∨ ((p4 ∨ ((p3 ∧ p4) ∧ p1)) ∨ True)) ∧ ((True ∧ (True → (p2 → True))) ∧ ((p5 ∨ ((p2 → p3) ∨ True)) → p2))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40975017577432634441787262438 : (((((p3 ∧ p4) ∧ (p2 ∧ ((p4 ∧ (False ∨ True)) → (True ∧ ((p2 → False) → (p1 ∧ ((p2 → True) ∨ p4))))))) ∨ (p1 ∨ p5)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164944170962096950576616127282 : ((((((True ∨ ((p1 → False) → (((p3 ∧ p3) ∨ p2) → p3))) ∧ True) → p1) → p5) → p2) ∨ ((((True ∨ p1) ∨ p2) ∨ (p5 ∧ p4)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258757376792981041002202366655 : ((True → False) → ((((p1 → (p2 ∧ ((p4 ∨ (False ∨ False)) ∨ (p1 ∧ (True → False))))) → (False ∧ (p4 ∨ (p4 → (True → p1))))) ∨ p3) ∧ p1)) := by
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
theorem thm_5_vars_245150074866761480843208365279 : ((p2 ∧ True) ∨ (p2 → ((p3 ∧ (p2 ∧ ((p5 ∨ ((((True → (((p2 ∧ p1) ∨ p4) → p2)) ∨ (p5 ∨ p4)) ∧ False) ∨ False)) ∨ p1))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157661234775959231128154646792 : ((((p1 → (p2 ∨ (p2 → (False ∧ ((p5 ∧ p2) ∧ (p2 → False)))))) → p1) ∨ (p1 ∧ (p3 → p2))) ∨ (p1 → (p4 ∨ ((True ∨ p3) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113017060503539480237563315726 : (((p5 ∧ (((p4 ∧ p3) → True) ∨ ((((True → ((p4 ∨ ((p1 ∨ p4) ∨ True)) ∧ p3)) → (p2 → False)) ∧ True) ∧ p4))) → p2) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654536950702604617971939933408 : (((((p5 ∧ (((((p3 ∨ p5) ∨ p5) → p1) ∨ p5) → (((p5 → True) ∧ (p3 ∧ p1)) ∧ (p2 → (p3 ∧ p5))))) ∨ False) ∨ (p4 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776473349008317584725978421048 : (((p1 ∨ (((((((p2 → (((False → p1) ∨ p4) → ((True ∧ p2) ∨ p5))) ∨ True) → p3) → (p4 ∨ True)) ∨ p1) → (p1 → p2)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_948923208305519239739559847444 : (((((p4 ∧ p4) ∧ p4) ∧ ((p1 ∨ (((p5 ∨ p4) → True) ∧ p1)) ∧ (((True ∧ ((True ∨ p1) ∨ p1)) → (p1 ∧ False)) ∧ (True ∨ p4)))) → p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h14 : (True ∧ ((True ∨ p1) ∨ p1)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h15 := h11 h14
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h18 : (True ∧ ((True ∨ p1) ∨ p1)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h19 := h11 h18
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h9.left
    let h25 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h27 : (True ∧ ((True ∨ p1) ∨ p1)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h23
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h28 := h24 h27
      -- We need to get the right conjuct of h28 based on <expert-advice>.
      let h29 := h28.right
      -- False on the left can always be used.
      apply False.elim h29
    case inr h30 =>
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h31 : (True ∧ ((True ∨ p1) ∨ p1)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h23
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h32 := h24 h31
      -- We need to get the right conjuct of h32 based on <expert-advice>.
      let h33 := h32.right
      -- False on the left can always be used.
      apply False.elim h33
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_992272813851261976624003777994 : (((p4 ∧ (((p3 ∨ (p4 ∧ p4)) ∨ (p1 ∧ (p3 ∨ (p4 → p1)))) → ((True ∧ ((False → p2) ∧ False)) ∧ (p1 ∨ (p1 ∨ (p1 ∨ True)))))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 ∨ (p4 ∧ p4)) ∨ (p1 ∧ (p3 ∨ (p4 → p1)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119976424460324818711614902521 : ((((((p3 ∨ ((p5 ∧ (((p2 ∨ p3) → p3) ∨ p5)) ∧ (p3 ∧ p1))) ∨ p5) ∨ p5) → (((p1 ∧ p2) ∧ False) ∧ p4)) ∧ p4) → (p3 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (((p3 ∨ ((p5 ∧ (((p2 ∨ p3) → p3) ∨ p5)) ∧ (p3 ∧ p1))) ∨ p5) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_880045988413834436339574922045 : ((((p5 → (((((p2 → p5) ∨ ((p3 → p5) ∧ True)) ∧ ((p1 → p4) ∨ False)) → p3) ∧ ((p1 ∨ False) ∧ (p4 ∧ p3)))) ∧ (True → p5)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_24174237799054217027356099085 : (((False ∨ (p5 ∨ (True ∧ True))) → ((p5 → (p2 ∨ (p2 ∨ (p1 ∨ (((p2 ∧ p1) → p4) → (p5 ∨ p1)))))) ∨ (p5 → (p5 → p1)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172581201050044373042898377499 : ((((True → p3) ∧ p4) → (False ∨ ((p5 ∨ (p3 → p2)) ∧ (p4 → (p2 ∧ p2))))) ∨ ((True ∨ (p2 ∨ (((p3 ∨ p4) → p3) ∧ p1))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160160793108428746657620228257 : ((((p5 ∨ (p1 ∧ ((p2 ∧ p2) ∧ False))) ∧ ((((p1 ∧ p4) ∧ False) ∨ p5) ∨ p3)) ∧ (p5 → p2)) → ((p3 → (p2 ∧ (p5 → p1))) ∨ p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- False on the left can always be used.
        apply False.elim h10
      case inr h13 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h14 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h13
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h15 := h3 h14
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h17 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h18 := h3 h17
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h22.left
    let h25 := h22.right
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304215137717713448856972118138 : (p1 ∨ ((((p1 → (p5 ∨ (((p3 ∨ p3) ∨ (False ∧ (True → (((p1 ∧ p5) ∨ p3) → (True → True))))) ∧ (p1 → p3)))) ∨ True) → p4) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 → (p5 ∨ (((p3 ∨ p3) ∨ (False ∧ (True → (((p1 ∧ p5) ∨ p3) → (True → True))))) ∧ (p1 → p3)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233803639084297546865522999023 : ((p3 ∨ (p1 → p4)) → (False ∨ (((((p5 ∨ p5) ∨ p5) ∨ p1) ∨ False) ∨ (False → (((p5 → ((p2 ∧ p4) ∧ p3)) ∨ p4) ∨ (False ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586731319693600946672688432125 : (((((p1 ∧ ((((True ∨ False) ∨ True) ∧ ((((p3 ∨ (p1 ∨ (p3 → (p4 ∨ True)))) ∨ (False ∧ False)) ∧ p2) → p1)) → p5)) ∧ p3) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41118272161466862806348614507 : ((((p4 ∨ ((((p5 ∧ p4) → (p3 ∨ (p2 ∨ p5))) ∧ p1) ∨ (p1 ∧ (True → (False ∧ (p2 ∧ p3)))))) ∧ (p5 ∨ (p4 → True))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157700676002273746308007110965 : ((((p5 ∧ (False ∨ (p1 → (p1 → ((p5 ∨ p3) ∨ (p4 ∧ p3)))))) ∨ True) → (p3 ∨ (True ∧ p3))) ∨ (((p1 → (p4 → True)) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147393847748207174208779421551 : ((((((((p3 → p4) ∨ p3) → False) ∨ p1) → p2) → (((p2 → ((p5 ∧ p2) ∧ p5)) → p3) → p3)) ∨ p1) ∨ (True ∧ (p1 → (True ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_17959947873198117710534621906 : ((((((p1 → (True → (p3 → (p5 ∧ p3)))) ∨ p3) → p1) ∨ (((True ∨ False) ∨ (p2 ∧ True)) ∨ p4)) ∨ (p2 ∨ (p5 ∨ (p4 → p5)))) ∧ True) := by
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
theorem thm_5_vars_593685550825360653860264003142 : (((((((p2 ∨ (p2 ∨ (False → (p2 ∨ True)))) → ((True → p3) ∧ (p1 ∨ p5))) → (p5 ∧ p4)) ∧ ((p2 → (p2 ∧ True)) ∨ p3)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58684346877264607330681602921 : (((p2 → p1) ∧ ((True ∧ p3) ∨ (((((p3 ∨ (p5 ∨ (p4 ∨ ((p5 ∧ False) ∧ p2)))) ∨ (p1 → (p4 ∨ p2))) ∨ p5) → p2) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322204483329431202442452387773 : (p5 ∨ ((((((False ∨ ((((((p3 ∨ p2) ∨ ((False ∧ (p1 → p2)) → p4)) ∧ p1) → p3) ∨ True) ∨ False)) → p4) → p3) → False) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63930590689371236911982905524 : ((False ∨ (((True ∨ (p4 → (False ∧ ((((p5 ∨ (p5 → p3)) ∧ True) ∧ False) ∨ ((p5 ∧ (False ∨ (False ∧ True))) → p5))))) → p3) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680262535965380459208089426055 : (((((p3 ∧ ((p4 → ((((p4 → p4) ∨ (p3 ∧ False)) ∧ p1) → p3)) → (p5 ∧ p5))) → (p4 → p4)) → (((p2 ∨ p5) ∨ True) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190501606281857241246952345593 : ((((True ∧ ((p5 → (p3 ∨ p2)) ∧ p3)) ∨ p3) → p5) ∨ (p3 → (((p5 ∧ (p2 → p5)) ∧ p4) → ((((p2 → False) → True) ∨ p2) ∨ p1)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114409972819894838556295201045 : (((((p4 ∨ p5) ∨ False) ∧ ((p1 ∨ p3) ∨ (((False ∨ ((p2 → p3) ∧ p2)) ∧ p4) ∧ p4))) ∨ (False ∧ ((False → p2) ∧ True))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65801286743245329752042098273 : ((p4 ∨ ((((True ∧ (p2 ∨ p5)) → p2) → (p1 → (p1 ∨ p4))) → ((p1 → ((False ∨ p4) ∨ (p4 ∨ p2))) → ((p5 → p4) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310249497709938722335530106167 : (p2 ∨ ((p1 ∧ ((p5 → (p1 → (p2 → ((False ∧ False) ∨ p2)))) → False)) → (((p2 → p2) ∨ ((p3 ∧ p1) → p1)) → (p3 ∧ (p4 ∨ p1))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p5 → (p1 → (p2 → ((False ∧ False) ∨ p2)))) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h6
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h1.left
    let h13 := h1.right
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : (p5 → (p1 → (p2 → ((False ∧ False) ∨ p2)))) := by
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- Implications on the right can always be decomposed.
      intro h17
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h18 := h13 h14
    -- False on the left can always be used.
    apply False.elim h18
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h1.left
    let h21 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h20
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h1.left
    let h24 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181115265554401484999466280892 : ((True ∧ (((p4 ∨ (p5 ∧ True)) ∨ ((p2 ∨ p1) ∨ p3)) ∧ (p1 ∨ p3))) → ((p4 ∨ (p1 ∨ True)) ∨ ((False ∨ (False → (True ∧ p3))) ∧ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h18 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h19 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h21 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h22 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h20
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h24 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h25 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126829581740205318587660791109 : ((p5 ∧ (((((p5 → p4) ∧ (p1 ∧ (p3 ∧ (p1 ∨ (p1 ∧ p3))))) ∧ (p3 → False)) ∨ p5) → (False ∧ ((p3 → False) ∨ p3)))) → (p1 ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((p5 → p4) ∧ (p1 ∧ (p3 ∧ (p1 ∨ (p1 ∧ p3))))) ∧ (p3 → False)) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : ((((p5 → p4) ∧ (p1 ∧ (p3 ∧ (p1 ∨ (p1 ∧ p3))))) ∧ (p3 → False)) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684915681983849777010772437159 : ((((p1 ∧ ((((p3 ∨ False) ∧ p3) → ((p5 ∨ p1) ∨ (False ∨ (p4 ∨ p3)))) → (False ∧ p4))) ∨ ((False ∨ p4) → (p4 ∨ (p4 ∨ p2)))) ∨ p1) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264999696851957515398530813350 : (True ∧ ((p2 → p2) → ((((True → (False → p5)) → p1) → (p2 → p3)) → (((p5 → p3) ∧ ((False ∨ (True ∨ p4)) ∨ p1)) ∨ (p4 → p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47261091408462220860320286478 : ((((((p5 → p2) ∧ False) → (False ∨ False)) → (((p5 ∨ p4) ∧ True) → ((((True ∧ p4) → False) ∧ (p2 ∨ p2)) ∧ p2))) ∨ (False → p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321595166683832863160300988020 : (p4 ∨ (p3 → (((p1 → (((((p5 ∨ (False ∨ ((p1 → p5) ∨ False))) → False) ∨ p2) ∨ (((False ∧ True) ∨ p4) ∨ p1)) ∧ p3)) ∧ True) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151816329544436601855697092624 : ((((((p1 → p2) ∨ p1) ∨ p5) ∧ (((p1 ∧ p5) ∧ True) ∧ (p1 → False))) ∧ ((p2 ∧ p5) → (p4 ∧ p3))) → ((p1 → p2) ∨ (p5 ∧ p4))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h5.left
      let h9 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h14 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h15 := h9 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h5.left
      let h18 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h23 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h24 := h18 h23
      -- False on the left can always be used.
      apply False.elim h24
  case inr h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h5.left
    let h27 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h28 := h26.left
    let h29 := h26.right
    -- Conjunctions on the left can always be decomposed.
    let h30 := h28.left
    let h31 := h28.right
    -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
    have h32 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h30
    -- We have shown the premise of h27, we can now drive its conclusion.
    let h33 := h27 h32
    -- False on the left can always be used.
    apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198384061471499919048925944224 : ((p3 ∧ ((p5 ∨ False) ∧ (p3 → (p3 → p1)))) ∨ (((p1 → (p3 ∨ (p1 ∧ p1))) → p1) ∨ (False ∨ (False ∨ (((True → p3) ∨ True) ∨ p3))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799800621885752749016156317244 : (((p1 → (p3 → (((((p3 ∨ (((p2 ∨ (p2 → p4)) ∧ p1) → ((True ∨ p3) ∨ p4))) ∧ p2) ∧ (False ∨ (p2 → True))) ∧ p5) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257479279917443642076203270023 : ((p3 ∨ True) → (p3 → ((p1 ∧ (p1 ∨ (True ∧ (True → (True ∨ (True → p2)))))) → (((p2 → (p2 ∨ (False ∧ (p5 ∧ p3)))) → False) → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h9 : (p2 → (p2 ∨ (False ∧ (p5 ∧ p3)))) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h11 := h4 h9
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h13 : (p2 → (p2 ∨ (False ∧ (p5 ∧ p3)))) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h15 := h4 h13
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h19 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h20 : (p2 → (p2 ∨ (False ∧ (p5 ∧ p3)))) := by
        -- Implications on the right can always be decomposed.
        intro h21
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h22 := h4 h20
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h24 : (p2 → (p2 ∨ (False ∧ (p5 ∧ p3)))) := by
        -- Implications on the right can always be decomposed.
        intro h25
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h25
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h26 := h4 h24
      -- False on the left can always be used.
      apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54285504670208488367887670313 : ((((p3 ∧ (p5 → p3)) → ((p5 → p1) → True)) ∧ (False ∨ (p2 ∨ (((True ∨ True) ∨ (((p3 ∨ p3) ∨ True) ∨ p4)) → (p2 ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50134860733426743452530476159 : (((p5 ∨ ((((((False ∧ True) ∨ (False ∨ False)) → False) → (p2 → p3)) ∧ True) ∨ (p2 ∨ (p5 ∨ p3)))) ∧ (((p5 ∧ False) ∧ p2) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160865250735442728629118780243 : (((False ∨ ((False → p2) → False)) ∧ ((p3 ∨ True) ∧ (((p4 ∨ False) ∧ p5) → ((p3 → p3) ∨ p5)))) → (((p5 ∨ (p1 ∨ False)) → True) → False)) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h4.left
    let h8 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h10 : (False → p2) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- False on the left can always be used.
        apply False.elim h11
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h12 := h6 h10
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h14 : (False → p2) := by
        -- Implications on the right can always be decomposed.
        intro h15
        -- False on the left can always be used.
        apply False.elim h15
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h16 := h6 h14
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726343296104196639939618501779 : (((((p4 ∨ p1) ∨ p4) ∨ (True ∧ ((((p5 ∧ p5) ∧ (p4 ∧ (False ∧ p3))) → (p5 → (p4 ∧ ((p5 ∧ True) ∧ True)))) → (p2 ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114923767084998031694984413168 : (((((((p4 → (False ∧ p5)) ∧ p1) → (False ∧ False)) ∧ p4) ∧ (True ∨ True)) → (((False → (p3 ∨ (True → p4))) → p3) ∧ p4)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212506527461948043687968372145 : ((p4 ∨ (True ∧ (p5 ∨ True))) ∧ ((True → (((False ∧ p3) ∨ ((p1 ∨ p3) ∨ (p3 → ((False ∧ p4) → ((True → p5) ∧ p3))))) ∧ p1)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234583883413321407555646014959 : ((p3 → (False ∨ p3)) → (((((True → (p2 ∨ True)) ∧ (p5 ∧ (p4 ∨ p4))) ∨ ((True ∧ p2) ∨ (True → p5))) ∨ (False ∧ (p5 ∨ True))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187434222867912493116447690193 : ((p5 ∧ (True ∧ (p3 → (p4 → (((p2 ∧ False) ∧ True) ∧ p2))))) → (((((((p5 → False) ∨ p3) ∨ p3) → p4) ∨ False) ∨ True) ∧ (p4 ∨ p5))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46388321745319877763284994170 : ((((p5 ∧ (p5 ∧ (((True ∧ (True ∧ p3)) → p5) ∧ False))) ∨ (((p3 → (False ∧ p1)) ∧ (False ∧ (True → p4))) ∨ p3)) ∧ (True ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45653356149361798382830067874 : (((p4 ∨ (p3 ∨ (((p5 → p5) → False) ∧ ((p1 ∧ p1) ∨ (p4 → ((True → (p5 ∧ False)) → (p2 ∧ (p4 ∧ (p3 ∨ p1))))))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321195123322269094313425316445 : (p4 ∨ (p3 ∨ ((True → (((((p3 ∨ p5) ∧ False) ∧ p3) ∧ False) ∨ p2)) ∨ (p4 → (((False ∧ (True → p5)) → (p5 → (p4 ∧ True))) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172907986789491972254512520951 : ((p2 ∧ ((p2 → ((p1 → (False ∧ (False → False))) ∧ p3)) → (p2 ∨ (p1 → p4)))) ∨ (((False ∨ ((p2 ∨ (p1 ∨ p4)) ∨ p4)) ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171720137727897840103852713355 : (((((p2 → (p2 ∧ (p3 ∧ (False ∧ (p3 → p1))))) ∨ (p5 ∨ p2)) ∧ p4) → False) ∨ (((False ∧ p2) ∧ True) → (False → (True ∨ (p1 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216576435991309753502250012806 : ((((p2 ∨ True) ∧ p3) ∧ p3) → ((((p5 → p3) ∧ ((p2 ∧ (p3 ∨ (p4 ∧ False))) ∨ ((False ∨ p1) ∧ p1))) ∧ p4) ∨ ((p3 ∧ False) → p4))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2383767141396613724579020718 : ((p3 ∨ (p2 ∨ (((True → p5) → ((p2 ∧ False) ∧ p1)) → p5))) ∨ (p2 → ((p4 ∨ p3) ∨ ((p1 ∨ ((p4 ∨ p3) ∧ p2)) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201139427657191383874513477086 : ((False → (((False ∨ (True ∧ p5)) ∧ p4) → p5)) → ((((p2 ∧ p3) ∧ ((False → (True ∨ p4)) → False)) ∧ (p1 ∧ p5)) ∨ ((p4 ∨ p1) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232716875973174112965875406756 : ((p1 ∧ (p4 ∨ p2)) → (p3 → ((((p3 ∨ (p2 ∨ False)) → ((p3 ∨ p4) → ((p2 ∧ True) ∧ (p4 ∨ True)))) → p4) ∨ ((p5 ∧ p1) ∨ p2)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134496231031718795018911140961 : (((((((((False ∧ True) ∨ (p4 ∧ (p3 ∧ p4))) ∧ False) → (False ∨ p5)) ∨ p1) ∨ (p1 ∨ (p1 ∧ p5))) ∨ p1) → False) ∨ ((False ∧ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98910950435390193025602580121 : ((True → (((((p4 ∧ ((p1 ∧ (p3 → (((p2 ∧ p4) ∨ (p3 → p4)) → False))) ∧ p4)) → (p2 ∨ True)) ∧ False) ∧ p3) ∧ (p4 → p1))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56312283535394161996724355934 : ((((p4 ∧ (p1 → p4)) ∧ True) → ((((p3 → False) ∨ p2) ∧ p1) ∨ ((p2 ∧ p5) ∨ (False → (((p3 → True) ∨ p3) ∨ (p2 ∧ p4)))))) ∨ False) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343573180955632366476804856379 : (p2 → ((True → False) → (True ∧ (((p4 → (((p3 ∧ p1) ∧ p1) → p4)) → p4) ∨ (False → (p3 ∧ (((p5 ∧ p2) → (True ∨ False)) ∧ p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299370574322433838207800568472 : (False ∨ (((False ∨ p2) ∨ (p1 ∧ (True → ((p1 → (p5 ∨ (p4 ∧ ((p4 ∧ False) → (False ∨ ((True ∧ False) ∨ (False ∧ p5))))))) ∨ p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179704887195820317561130779110 : (((((p4 → (False ∧ False)) ∨ (p3 → (p3 ∧ (p3 ∨ p3)))) ∨ p1) ∧ p1) → ((((p2 → (((p4 ∧ True) ∧ p4) ∨ True)) ∨ p4) ∨ p2) ∨ False)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57050037119617317459952973880 : (((p3 → (p1 → p3)) ∧ (((((p1 → p5) ∧ ((False ∧ ((p2 → p2) → (p3 → p2))) ∨ p5)) ∨ ((False ∧ p5) ∨ p1)) ∨ True) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135347474648913629069572029870 : (((p2 ∧ (((p4 ∨ p3) ∧ ((((p3 ∨ p2) ∨ False) ∨ ((False → p1) ∨ p2)) ∧ p2)) ∨ p1)) ∧ (p4 ∨ (p4 ∨ p3))) ∨ (True → (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115548863158370723976732735017 : (((p5 → (True → ((p4 → (p3 ∧ True)) → p2))) → (p3 → (p1 ∧ (p2 ∨ ((False ∨ True) ∧ (p4 ∨ (p3 ∨ (p1 ∨ True)))))))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750263353721412995903712381689 : (((True ∧ (((((p1 ∧ p4) ∧ p3) → (p3 ∧ (False ∨ (p5 ∨ (p3 ∨ p3))))) → ((p2 ∨ ((p2 ∧ p5) ∨ p2)) ∧ p5)) ∨ (p1 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47712132220602925210662980216 : ((((((False → ((p1 ∧ p4) ∧ (((p5 ∧ (p4 → (p3 ∨ (p1 ∨ p2)))) ∧ p4) ∧ (p1 ∨ True)))) ∨ p3) ∨ p3) ∨ p4) → (p4 → p4)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h6 =>
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148119203800749560824055170801 : ((((((p3 ∧ False) ∧ p3) → False) ∧ (((p1 ∨ p2) ∨ (p4 ∧ (p3 ∨ (p2 → False)))) ∨ p3)) → (False ∨ True)) ∨ (p4 ∨ ((False ∨ p3) ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51103149357828997785768815616 : ((((p1 ∧ ((((p2 ∨ p3) ∧ p1) ∧ p3) ∨ ((((p4 → p2) → p4) ∨ True) ∧ p4))) ∧ p3) ∨ (True ∨ ((p1 → p5) → (p1 → False)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66058558672613426177469797158 : ((p5 ∨ (((True ∧ ((((p4 ∧ p2) ∧ ((True → p5) → (p5 ∨ p1))) ∧ (p3 ∧ p3)) ∨ (p3 → (False → p3)))) ∨ (p3 → p1)) ∨ False)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672792468954447839244812491444 : ((((((((((False ∧ False) ∧ (p3 ∨ p1)) ∨ p4) → (p2 ∨ (p2 ∨ False))) ∧ True) ∧ p2) ∧ (p3 → (p5 → True))) → ((p2 → True) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624220267883885310043998844917 : ((((p3 ∨ (((p5 ∧ (True → ((False ∧ False) ∧ ((p1 ∨ (p2 ∧ (p3 ∧ ((p3 → p3) → (False ∧ True))))) ∧ p2)))) ∨ p3) ∨ False)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52878942649641644081304220976 : (((True ∨ ((p1 → (True → (p5 ∨ p1))) ∨ ((p2 ∧ p1) ∨ (p1 → p3)))) → (((p5 ∧ ((p3 → (p4 ∨ p2)) → False)) ∧ p4) → p3)) ∨ p2) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : (p3 → (p4 ∨ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h8
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h13 : (p3 → (p4 ∨ p2)) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h15 := h6 h13
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h20 : (p3 → (p4 ∨ p2)) := by
          -- Implications on the right can always be decomposed.
          intro h21
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h22 := h6 h20
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h24 : (p3 → (p4 ∨ p2)) := by
          -- Implications on the right can always be decomposed.
          intro h25
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h26 := h6 h24
        -- False on the left can always be used.
        apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134895863307928500026206863654 : (((p5 → (((p4 ∨ p3) ∨ (p3 ∨ True)) ∧ (((p1 → (p1 ∨ ((p3 → p5) → (p1 ∨ p3)))) → p2) → p5))) → False) ∨ ((True ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134086089162889086517625152490 : (((((True → (p2 ∨ p3)) ∧ ((p5 ∨ ((p1 ∧ p2) ∧ ((p3 ∧ (False ∨ (p2 ∨ p5))) → p2))) → False)) → False) ∨ p5) ∨ (p5 → (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68085748547403027548403958270 : ((p2 → (p4 ∨ (p4 ∧ ((((p2 ∧ (p5 ∧ p2)) → p2) → ((((((False ∨ p1) ∧ p5) → True) ∨ p5) ∨ (p1 ∨ p4)) ∨ p1)) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745949891816736462705497203654 : ((((False ∨ p4) → (((((p4 ∨ p2) ∧ p4) → p3) ∨ ((p4 ∨ p2) ∧ (((True ∨ p3) → p2) → (False ∨ (p3 → p5))))) ∧ (p1 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_842432765479631922721157606 : ((False ∨ ((p2 ∧ True) ∨ ((p3 → p1) ∨ ((((p4 ∧ (p5 ∨ (False ∧ ((p4 ∨ p3) ∧ (False → p3))))) → True) ∧ p5) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337105258382020085233551849840 : (p1 → (((p4 ∧ (p4 ∨ p2)) ∧ (p1 ∧ (((p3 ∧ (((p4 → p4) ∧ False) ∧ (True → p2))) ∨ (p1 ∧ (p5 ∧ p4))) ∨ p4))) ∨ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68845399952653021205650574965 : ((p4 → ((p5 ∧ p2) ∨ (((((True → p2) ∨ p4) ∨ ((False ∧ (p5 ∨ (p4 ∧ True))) → (p5 ∧ (p4 ∧ False)))) → (False ∨ p2)) ∨ True))) ∨ False) := by
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
theorem thm_5_vars_305853673752305181683329817886 : (p1 ∨ ((p4 ∨ (((p3 ∧ p3) ∧ p5) → p5)) ∧ (((p1 → ((p1 → ((((p5 ∧ p2) ∧ False) ∧ p5) ∧ p5)) ∨ (True ∨ p2))) ∧ True) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306248009097657242058792034068 : (p1 ∨ ((p4 ∧ (p1 ∨ True)) → ((((((p4 → p5) ∨ p5) → ((p4 ∧ p1) → False)) → (p5 → False)) → p5) → (((p1 ∨ p5) ∨ p2) ∨ p4)))) := by
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
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160665211302033113248017744808 : (((True ∨ (True ∧ ((True → ((p5 ∨ p1) ∨ p4)) ∨ p1))) → (((True ∨ p2) ∧ False) ∧ (p4 ∨ p5))) → ((p2 ∨ (p2 ∨ p1)) ∨ (p5 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (True ∧ ((True → ((p5 ∨ p1) ∨ p4)) ∨ p1))) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190339366284848922722827103685 : ((((True ∧ (p5 ∨ p2)) ∧ ((p5 ∧ p5) ∧ p2)) ∨ p1) ∨ ((p4 ∧ (p3 → (p2 ∧ p5))) → (p4 ∧ ((p5 → p4) ∨ (p4 → (False → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140462922020293561265101769969 : (((p1 ∨ ((p2 → ((False ∧ (p4 ∧ (((p3 ∧ p3) ∧ p3) ∧ p1))) ∧ p2)) ∧ (p3 ∧ False))) → ((p4 ∨ p2) ∨ p4)) → (p5 → (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757585476887986843715934489608 : (((p1 ∧ (p3 ∧ (((False ∨ (((p2 ∧ ((False ∧ p4) ∧ p1)) → (p4 → (((p4 ∧ (p1 → p1)) ∧ p1) → False))) → False)) ∧ p1) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265637371591998018188037424921 : (True ∧ (p2 ∨ ((True → (((((((p2 ∧ (((p2 → (p4 ∧ p2)) ∧ p3) ∨ p2)) ∧ (p1 ∨ p1)) → False) → p4) ∨ False) ∨ True) ∧ p5)) ∨ True))) := by
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
theorem thm_5_vars_156730146281968453782992131884 : (((((p3 ∨ p3) ∨ ((p1 ∧ False) ∧ p3)) → ((p3 ∨ ((True ∧ p5) ∨ (p4 ∨ p3))) → p5)) ∧ p3) ∨ ((False ∧ p2) → ((p2 ∨ p4) ∧ p1))) := by
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
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



