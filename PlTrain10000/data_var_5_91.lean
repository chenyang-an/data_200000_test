variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47743932211238864317569400205 : ((((((p4 → p4) → (((p3 → True) ∧ p5) ∧ p1)) → (((p1 ∧ (p3 → (p3 → (p1 → p1)))) ∨ p1) ∧ p5)) ∨ False) → (p1 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178699231864109256147454395060 : ((((p1 → p3) ∨ (True ∧ p2)) ∨ (p2 ∧ ((p3 ∧ (p5 ∧ False)) ∧ p3))) ∨ ((False ∨ (((p2 → p5) ∧ False) → (p3 → p1))) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186721868404505677047046776772 : (((p2 ∧ (((p1 ∧ p3) ∨ False) → p1)) ∨ (p5 ∧ (p5 ∧ False))) → ((((p2 → (((p4 ∧ p4) ∧ p5) ∨ p4)) ∧ p2) → p3) ∨ (p2 ∧ True))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142358254377601405361503366473 : ((p3 ∧ (p5 ∧ (((p2 ∨ p5) ∨ (p2 → p2)) ∨ ((p1 → (False ∧ ((True ∨ ((True ∨ p4) ∧ False)) → p4))) ∨ p1)))) → (p1 → (False ∨ True))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262403617592848336863043705262 : (True ∧ (((p5 → p4) → (((((p1 ∨ ((True → p4) ∨ (True ∧ p5))) ∧ p2) → ((p3 ∧ p4) ∧ ((p5 → p4) ∨ p1))) → p2) ∨ p3)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117951083599694413537168951531 : ((p5 ∧ (p1 ∨ (((((False → ((True ∨ (p2 → True)) ∨ (p1 ∨ p3))) → p1) ∨ p3) ∨ ((p1 ∧ (p1 → True)) → False)) ∧ p5))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214794289863177330851958682647 : (((p1 ∨ p3) ∨ (p5 ∨ p4)) ∨ ((((p3 ∨ ((p5 ∧ (True ∧ p4)) ∧ p2)) → (p2 → ((p4 → ((p1 ∨ p1) → p2)) ∧ p5))) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151183414779424584039534717463 : ((((((p3 ∨ (False → p2)) ∨ p4) ∨ (p3 ∨ (True → p3))) → (((p4 → (p3 ∧ True)) ∧ p4) ∨ p3)) → p5) → ((p2 ∧ (p2 → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183990223503447316855611927122 : (((((p2 ∧ False) ∧ ((p4 ∧ (p3 ∧ p4)) ∨ p1)) ∧ False) ∨ p1) ∨ ((p1 ∧ p5) → (((p4 ∨ (p5 ∨ (p1 ∧ p3))) → p4) → (True → p4)))) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (p4 ∨ (p5 ∨ (p1 ∧ p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615218980593171943556115767352 : (((((False ∧ (((p3 ∧ p4) ∨ ((False ∧ p4) ∧ ((False ∧ p2) ∨ (p5 → False)))) ∨ p5)) ∧ ((((p2 → p1) ∨ p2) → p3) ∨ True)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_134392232156770959777861411822 : (((True → ((((p3 → (p3 ∨ (((True → p4) ∨ True) ∨ p2))) ∧ (True → ((p4 → p1) ∧ p3))) ∨ p3) ∧ p2)) ∨ False) ∨ ((p1 → p1) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164884899021983703394133711096 : (((p2 → (p1 ∨ ((p4 ∨ ((p2 ∧ (p3 ∨ p1)) ∧ ((p4 ∨ p1) ∧ p1))) ∨ p3))) ∨ p3) ∨ (True ∨ (((p5 ∧ (p4 ∧ p3)) ∧ p1) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48794347643957391779452579003 : (((False ∧ (((True ∧ p4) → (p2 ∧ ((True → False) ∧ p3))) ∧ (True ∧ (((p4 ∨ p2) ∨ p2) ∧ (False → p3))))) ∧ ((p5 ∨ p2) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52769155003258508525872306985 : ((((p2 ∨ ((False ∧ ((False ∨ p4) ∨ True)) ∧ ((p5 → p2) ∧ p3))) → p2) → (((p3 ∨ p2) → ((p1 ∧ p4) ∨ p1)) ∧ (True ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208598795251493111908619865157 : (((p3 → p2) → ((p2 ∧ p3) ∧ p4)) → (p2 ∨ (((p5 ∧ ((p1 → (p3 ∨ p4)) → False)) → (p3 ∧ (((p1 ∨ p5) → True) ∧ p5))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p3 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : (p1 → (p3 ∨ p4)) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h7
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h5
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- One of the premise coincides with the conclusion.
  exact h12
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h13
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h14 := h2.left
  let h15 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324258191134778899113615269462 : (p5 ∨ ((((True ∨ True) ∧ (True ∧ (True ∧ p4))) → p5) ∨ ((p4 → (((p5 ∨ ((True ∧ p4) ∨ True)) ∧ False) ∧ (p4 ∧ True))) ∨ (True ∨ True)))) := by
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
theorem thm_5_vars_646178481450064369631701620163 : ((((False → (((p1 ∨ ((p5 ∧ ((((False ∨ p2) ∧ False) ∧ (p4 ∧ False)) → True)) → (((p3 ∧ p5) ∨ p1) ∧ p5))) ∨ p3) → p4)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134576321689108525021920817196 : ((((p4 ∧ ((((((p5 ∨ ((p3 ∧ p4) ∨ p4)) ∧ (False ∧ False)) → p5) ∨ True) → p4) → p3)) ∧ (p3 → p2)) → False) ∨ ((False ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186577423219958049070265041817 : (((p4 → (((p5 ∧ p5) ∨ (p1 ∨ p1)) ∨ p1)) ∨ (p4 ∨ p5)) → (((True ∧ p3) ∧ ((((p4 ∨ True) → p1) ∧ False) ∨ False)) ∨ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589782983604859977862365048648 : ((((((p4 → ((True ∧ (((p3 ∨ ((p1 → p3) ∨ p5)) ∧ (False → p3)) → (p1 ∨ (p3 ∧ p3)))) → p3)) ∨ (p1 → p1)) → p4) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215264316630059866792209978333 : ((False ∧ (p1 ∨ (p2 ∧ p4))) ∨ (p1 → ((((p4 ∨ (p1 ∨ p4)) ∧ (p2 ∧ (p3 → p4))) ∧ p4) → ((p5 ∨ ((p4 ∧ False) → p5)) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h6.left
      let h16 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h6.left
      let h22 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- False on the left can always be used.
      apply False.elim h25
  -- Conjunctions on the left can always be decomposed.
  let h26 := h2.left
  let h27 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h28 := h26.left
  let h29 := h26.right
  -- Disjunctions on the left can always be decomposed.
  cases h28
  case inl h30 =>
    -- Conjunctions on the left can always be decomposed.
    let h31 := h29.left
    let h32 := h29.right
    -- One of the premise coincides with the conclusion.
    exact h27
  case inr h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h29.left
      let h36 := h29.right
      -- One of the premise coincides with the conclusion.
      exact h27
    case inr h37 =>
      -- Conjunctions on the left can always be decomposed.
      let h38 := h29.left
      let h39 := h29.right
      -- One of the premise coincides with the conclusion.
      exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197100693442800340254906735214 : (((p4 ∧ (p4 ∨ ((p5 ∧ p4) ∧ True))) ∨ p3) ∨ (p2 → (p2 → ((((p5 ∨ p3) ∧ False) → (p1 ∨ True)) ∨ (((False ∧ True) ∧ p5) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336172314441927902015462477934 : (p1 → ((((p1 → True) → (True ∧ (p4 → (p5 ∧ (p1 ∧ (((p5 ∧ (((p3 → p3) → (p2 → p4)) ∧ p5)) ∧ p3) ∧ p5)))))) → False) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178257959725490160382024882948 : ((((p3 ∨ ((False → p2) ∧ (p4 ∨ (p4 → p3)))) → p3) ∧ (p4 ∧ p1)) ∨ (p1 ∨ (((p2 → p4) ∨ (((False ∧ p4) ∨ True) → p2)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329114845222992038213372410455 : (True → (((False ∧ p2) ∧ (p4 ∨ p3)) ∨ (p3 ∨ (((p1 ∧ (p4 ∨ ((p2 ∧ ((p4 ∨ p1) → (p2 ∧ p3))) ∧ p3))) ∧ (False ∧ True)) → False)))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h4.left
    let h9 := h4.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h4.left
    let h16 := h4.right
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172626048024433664627874265230 : (((p2 ∧ p2) ∧ (False ∧ (((p5 → p5) → p1) ∨ ((False → p3) → (p1 ∧ p3))))) ∨ (False → ((p2 ∧ (((p4 → p2) ∧ p3) ∧ False)) → p4))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590496108589111137529427975839 : ((((((p5 ∧ p2) → (p2 → ((((p4 ∨ (((p4 → False) ∨ (True ∨ False)) → (p3 ∨ p5))) ∧ p2) → (p2 ∧ p2)) → p5))) → p3) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761423007585870221635535866003 : (((p3 ∧ (((False → p4) → (((p2 ∧ p1) ∧ p2) → (p1 ∧ ((p4 ∧ True) → (((((p3 → True) → p3) ∧ False) → p2) → p3))))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144524483878977242952994227705 : ((((((p3 ∧ ((True → ((p1 ∧ True) ∧ (p3 ∨ p2))) → p3)) → True) ∧ (p4 → p4)) → p2) ∨ (p2 ∨ True)) ∧ ((False ∧ p2) → (p2 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59370057501258425761428291453 : (((p5 ∨ p4) ∨ (((p2 → p5) ∧ p4) ∨ (p2 → (False ∨ ((p2 ∧ (((p5 ∧ (p2 ∨ (p2 ∧ p5))) ∨ (p4 ∨ False)) → p4)) → p2))))) ∨ p1) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64735209290171325056675915476 : ((p2 ∨ (((((((p4 → p3) ∧ (p3 ∨ (p3 ∨ p3))) ∨ ((p5 ∨ (False → (True ∧ p4))) ∧ p4)) → (p2 → p5)) ∨ True) ∨ p2) ∧ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_354766469920696857228912673756 : (p5 → (((p2 ∧ ((False → p1) ∧ ((p1 ∨ ((False → p4) → p2)) ∧ p3))) ∨ ((p1 ∨ ((True ∧ p3) ∨ False)) ∧ ((p1 → p4) ∨ p5))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156912121093030253353722643550 : (((((((True → p5) ∧ (p4 → p5)) ∧ (((True ∨ p4) ∧ p3) ∨ True)) ∨ (p5 ∨ True)) → p2) ∨ True) ∨ (((p3 ∧ (True ∧ p2)) → p4) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787431445512491704946264121620 : (((p4 ∨ (p5 ∧ (((((False → p5) ∨ p2) → (p5 ∧ True)) → (((((p3 → p5) → p1) ∨ True) ∧ p1) ∨ (False → p3))) → (p1 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161854075824948398136930068337 : ((True → (p5 ∧ ((True ∧ (((True → p3) → True) ∧ (True → p1))) ∧ (False → (p5 → (False ∨ True)))))) → ((p1 → False) → ((p3 → p5) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45436633193365056137349425802 : (((True ∨ (((True ∨ p5) ∧ (p2 → (p3 ∧ (p3 ∧ (((p3 → (p5 ∧ p5)) ∨ p2) ∨ (p3 → p5)))))) ∧ (p4 ∨ (p4 ∨ p2)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92330107902294838881278946909 : (((False ∨ True) → ((p1 → ((((p1 → p4) ∨ ((p2 ∨ False) ∧ p4)) ∧ ((p3 ∧ p1) ∨ (True ∨ p4))) ∨ (p3 ∧ (p4 ∨ False)))) ∧ False)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ True) := by
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
theorem thm_5_vars_240475467174105148043982220750 : ((p5 ∨ True) ∧ (p4 → ((((((p2 ∨ p5) ∧ (p1 → (((False → p4) ∨ p1) → p4))) → p1) → (p4 ∧ p5)) → ((p1 ∧ p5) ∨ p1)) ∨ p4))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171835911053389035772539414744 : (((((False ∧ p3) ∧ True) → ((True ∧ (p1 ∧ (p5 → p4))) ∧ (p5 ∧ p3))) → p4) ∨ (((((p4 → p1) ∧ (False ∧ p3)) ∨ False) → p3) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57924782032110761462063843206 : (((True → (p2 ∧ p1)) → ((True → ((((p2 ∧ p2) → ((p2 ∨ (((p5 ∧ p5) ∨ p5) ∨ True)) → (p3 → p4))) ∨ p4) → False)) ∨ p1)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61902408129402215837375172308 : ((p2 ∧ (((p1 ∨ (False ∧ False)) → ((p5 → True) → (p3 ∧ (True ∨ ((p2 ∧ (p3 ∧ ((p5 → p2) → p2))) → p3))))) → (p2 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116198206833335413271100463624 : ((((p2 ∨ p2) ∧ p1) ∨ (((p2 ∧ False) ∨ ((p3 ∧ ((False → p4) → p1)) → ((p2 ∧ p1) → (p2 ∧ (True ∨ p2))))) ∧ p2)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51722585815745198703681534118 : ((((p1 → (((p1 ∨ p1) ∨ p3) ∧ p3)) ∨ ((((p1 ∨ p1) → False) → True) → p3)) ∧ (p3 → ((p1 → ((True → True) → p1)) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118776660890989244502631404284 : ((p5 ∨ (False ∨ ((p1 ∨ (((p5 ∧ (p3 ∧ ((p5 → p5) ∧ p2))) → False) → ((p1 ∨ p1) ∧ False))) ∨ (True → (False → p1))))) ∨ (p3 ∨ p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669518307063688043958312358791 : (((((((p5 → True) ∨ p2) → (True ∧ (((True ∧ p5) ∧ (p3 → (False → p4))) ∧ (False → p4)))) → (p4 → p3)) ∨ ((p5 ∨ p4) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336295861550171215760635264968 : (p1 → (((p5 ∧ ((p5 → (p2 ∧ p2)) → (p4 ∨ True))) → (((False ∨ (p3 ∧ ((p4 → p5) ∧ p3))) → (p2 ∨ (p4 ∨ True))) ∨ p2)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199419601803896958467673430834 : ((((p3 ∧ p1) → ((p4 ∨ False) → True)) ∨ p3) → (p1 → ((((((p1 ∨ True) ∧ (False → True)) ∨ p1) ∧ (p3 ∨ p2)) ∨ (p1 → p5)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214489549188306868502402404175 : (((p2 ∧ True) ∧ (p1 ∧ False)) ∨ ((((p2 → (False ∨ (((p5 → True) → p3) → ((p2 ∨ p5) ∧ (True ∨ p1))))) ∧ False) ∧ (p3 ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77005149643946341372945432477 : (((((((True ∨ p3) ∧ p5) ∨ p2) ∨ p1) ∨ ((True → False) ∨ ((p3 ∨ (False → p4)) ∧ ((((False ∨ p2) ∧ p1) → p5) ∨ True)))) → False) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((True ∨ p3) ∧ p5) ∨ p2) ∨ p1) ∨ ((True → False) ∨ ((p3 ∨ (False → p4)) ∧ ((((False ∨ p2) ∧ p1) → p5) ∨ True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614161448025741573110964734595 : (((((((((p1 ∨ (((p2 ∨ ((p3 → p1) ∨ p5)) ∨ p4) ∧ (True ∧ True))) → False) ∨ False) ∧ p2) ∨ p2) → ((p4 ∨ True) → p1)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_103006705347530923421203899111 : (((((((p4 → ((p1 ∨ True) ∨ p3)) ∧ p2) ∨ False) → False) ∨ ((p3 ∨ (p2 ∧ (p5 ∨ (False ∨ (p5 ∨ True))))) → True)) ∨ True) ∧ (p2 → p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54803263447397967391831802322 : (((p1 ∨ (((True → p5) ∨ (p2 ∨ p2)) → p5)) → (False ∨ (p1 ∧ (((p2 ∧ False) ∨ True) → ((p2 ∧ ((p4 ∨ p1) → p1)) → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260054782306762845061723857908 : ((p2 → False) → (((((p5 ∨ ((p5 ∨ p4) ∧ (p2 ∧ (p2 ∨ p2)))) ∧ False) ∨ p1) ∧ ((p3 → (p5 → True)) ∨ p1)) ∨ ((True ∧ p1) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_702345004351979178645710108497 : (((((((True → (p3 → (p5 ∨ p2))) ∧ p2) ∨ p1) ∨ False) ∨ (((p2 → (True ∧ ((p5 → (p2 ∧ p1)) → (p3 ∨ False)))) ∧ p4) → True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336587538234629485220667775061 : (p1 → ((((p3 ∨ (((False ∧ p1) ∨ (p3 ∧ (((True ∧ p5) ∧ p3) ∧ p4))) ∧ p4)) → ((False ∧ p4) ∨ ((False ∨ p4) ∨ p1))) → p4) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 ∨ (((False ∧ p1) ∨ (p3 ∧ (((True ∧ p5) ∧ p3) ∧ p4))) ∧ p4)) → ((False ∧ p4) ∨ ((False ∨ p4) ∨ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- False on the left can always be used.
        apply False.elim h10
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h15.left
        let h18 := h15.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h17.left
        let h20 := h17.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h21 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709200196989347031000144354123 : (((((p4 ∨ p3) ∧ ((p2 → p2) ∧ (p3 → p4))) → ((p4 ∧ (False ∨ (p1 ∨ (p5 ∧ (p5 ∨ (p3 ∨ p5)))))) → (False ∧ (p2 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248793000680704400191625255974 : ((p3 ∨ p3) ∨ (p1 → (((p1 → ((False ∨ ((p3 ∨ (False ∨ (True ∨ False))) ∨ p5)) ∨ ((p4 → (p5 → (p1 ∧ p1))) ∧ p3))) ∧ p1) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68247886879699455166978044893 : ((p3 → ((p1 → (p1 → (p4 → (p5 ∨ ((p5 → p2) ∨ (((p4 ∧ p2) ∨ ((p4 → (p3 ∨ False)) → False)) → (p4 → False))))))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175351268312719842506158045746 : ((p5 ∨ ((False → (True → ((p1 ∧ True) ∧ p4))) ∨ ((p3 ∧ (p5 ∨ p3)) → p4))) → ((p2 ∨ (p1 ∨ ((False → p4) ∨ (p1 ∧ True)))) ∨ p2)) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321607542510779170224171394109 : (p4 ∨ (p3 → (((((p2 ∧ p1) ∧ (p3 → (True → ((((p4 ∨ (p5 → p3)) ∨ p3) → p1) ∨ p5)))) ∧ (p2 → p4)) ∧ True) ∨ (p2 ∨ True)))) := by
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
theorem thm_5_vars_304737943163889083708023884072 : (p1 ∨ (((((True ∧ False) → (p1 ∧ True)) ∧ p1) → (True → (p2 → (((p3 → ((p4 ∨ True) → p3)) → p3) ∧ (p1 → p5))))) ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742490269961107614434102338073 : ((((p2 → False) ∨ ((p1 ∨ (p5 ∧ (((True ∧ ((p3 → p4) → p4)) → (True ∨ ((True ∨ p5) ∧ False))) → p1))) → ((p3 ∧ p4) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264802841004501381860099760061 : (True ∧ ((p2 ∧ p2) ∨ (((((True ∧ (p4 ∨ p2)) ∨ (p1 ∧ p1)) ∨ (p2 ∨ p5)) ∨ True) ∨ (p4 ∨ (((False ∧ (p2 → False)) ∨ p4) ∨ p3))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787908191661753049272918297079 : (((p4 ∨ (p3 → (((p4 → ((p1 ∨ p3) → ((p4 ∧ p5) ∧ p2))) ∨ (p3 → (True → p1))) → ((p1 ∨ p1) ∨ (p3 ∨ (p1 ∨ False)))))) ∨ p4) ∧ True) := by
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
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300816125481616416565636772556 : (False ∨ ((((True → True) → ((p4 → (p1 ∨ True)) ∧ True)) ∨ (p5 → ((p1 ∧ True) → p5))) → ((p5 ∧ ((False → p2) → (p5 → False))) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (False → p2) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h6
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h12 : (False → p2) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h13
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h14 := h4 h12
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721822672794174434456960668066 : ((((p3 ∨ ((True ∧ p2) → False)) → ((p1 → (p3 ∧ p4)) → ((p5 ∨ ((p5 → ((p4 → ((p5 ∨ p2) → p3)) ∧ True)) → p1)) ∨ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_62160809755859173592704915899 : ((p2 ∧ (p2 → (((p2 → (p5 ∨ ((p3 ∨ p4) ∨ True))) ∧ p3) ∧ ((((p1 → p3) → p5) ∨ ((True ∨ (p1 ∨ p1)) ∧ p2)) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_914382567777227391126069318379 : (((((p3 → (((False ∧ (p2 ∧ False)) → p5) → (p4 ∨ p3))) ∧ (p1 ∧ (p3 ∨ p3))) ∧ (((p5 → p3) → (p1 ∧ (p3 → p4))) ∧ p1)) → p4) ∧ True) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h11 : (p5 → p3) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h13 := h9 h11
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h3.left
    let h19 := h3.right
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h20 : (p5 → p3) := by
      -- Implications on the right can always be decomposed.
      intro h21
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h22 := h18 h20
    -- We need to get the right conjuct of h22 based on <expert-advice>.
    let h23 := h22.right
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h24 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h25 := h23 h24
    -- One of the premise coincides with the conclusion.
    exact h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321312173780135404302562146927 : (p4 ∨ (p5 ∨ ((((p4 ∨ p5) ∨ (p1 ∨ (False → (((p2 ∧ p3) ∨ p1) → (True ∧ p4))))) ∨ p1) ∨ ((((False ∧ p2) ∨ p3) ∨ p1) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47206081622363192259535483049 : (((((False ∨ ((True → (p2 ∨ p1)) ∨ p5)) → (False ∨ p4)) ∧ (((p5 ∧ (p3 ∨ (p1 ∨ (False → p5)))) ∧ p5) ∧ p1)) ∨ (False → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310388092414351511309965081633 : (p2 ∨ (((((p4 ∨ (p5 ∧ p1)) ∧ False) → False) → False) ∨ ((p3 → True) ∨ (((p5 → p1) ∧ ((p5 ∧ False) ∨ p4)) → (True ∧ (p4 ∧ p3)))))) := by
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
theorem thm_5_vars_41345230353429576616475921644 : (((((p3 ∨ p3) ∧ ((((p3 ∨ (True ∨ p4)) ∧ ((p3 ∨ p1) ∨ True)) ∨ p2) ∨ False)) ∨ (p3 ∨ ((p4 ∨ (p4 → False)) ∧ p4))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309656143043171634316557147804 : (p2 ∨ ((p4 ∨ (((p2 ∧ (p3 ∧ (p3 → p2))) ∧ ((((p4 → p5) ∧ p5) ∧ (p1 ∧ (p3 → p1))) ∨ False)) → p4)) ∨ ((p1 ∧ False) → p4))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138417879891746671382721438737 : ((p5 → (((((p3 → (((p4 → True) ∨ p5) ∧ True)) ∧ (p2 → ((p2 ∨ p4) ∨ True))) → p1) ∨ (True → p1)) → p2)) ∨ ((p3 ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153468900025861139333187917872 : ((p4 ∨ (p3 → ((False ∨ (((p2 ∨ False) ∧ p4) ∨ ((p3 ∨ False) → False))) ∨ (((p2 → p3) ∧ p5) ∨ p4)))) → (((False → False) → p3) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (False → False) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h4
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (False → False) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h8
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148799799553837529517094984720 : ((((p2 → (True ∨ (p1 → True))) ∧ True) → (((p3 → (True → True)) ∨ ((p2 ∧ (p5 ∨ p5)) ∨ p4)) → p3)) ∨ ((p4 → p4) → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41167038044378233479773272697 : ((((((((p4 → p1) ∧ ((p2 → p5) ∨ (p3 ∨ ((True ∧ p5) ∧ (p4 → p1))))) → True) ∧ p2) ∧ p5) → (p1 ∨ (p1 → p2))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114639391975008662194845153663 : ((((True ∨ (p2 → (((p3 → False) ∨ ((False → p5) ∧ p4)) ∨ (False ∨ False)))) → False) ∨ (p3 → (((True ∧ p4) ∧ p1) ∧ False))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228640834038342768623382574738 : ((p2 ∨ (False ∧ p3)) ∨ (p2 ∨ ((((True → False) ∨ False) ∧ (p4 ∨ False)) ∨ (((p5 ∨ ((p4 ∨ p3) ∧ (False → (True ∨ p1)))) ∨ p2) ∨ True)))) := by
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
theorem thm_5_vars_140935989309311151848053551312 : ((((((False ∨ p2) → p3) ∧ (p5 ∨ (False → p5))) ∨ p5) ∨ ((((True ∧ ((False ∧ True) ∧ True)) → False) ∨ False) ∧ p3)) → ((p3 ∨ True) ∨ p5)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171421286111490715168031992634 : ((((p3 ∧ p2) ∧ ((p3 → ((p3 ∨ True) ∨ ((False → p5) ∨ p1))) ∧ p4)) ∧ p4) ∨ (((False ∨ (p2 ∨ (p3 → p2))) ∨ True) ∨ (p2 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677817942170859945321787650849 : (((((((p4 ∧ (((True ∧ p5) ∧ p1) ∧ True)) ∨ ((False ∨ False) → p3)) ∧ (p1 → p2)) ∧ (False ∨ p1)) ∨ (True → ((p1 → True) ∨ p1))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262231709800853949068365820318 : (True ∧ (((((p1 → p3) ∨ ((p2 → p1) ∧ p2)) ∧ (((p1 ∨ (p5 → p3)) → (((p4 → True) → p3) → False)) ∧ p1)) ∨ (p3 ∨ p1)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117877920276980643332622233906 : ((p5 ∧ (((((True ∨ p5) → ((p4 → (((p4 → (True → p1)) ∨ p5) → True)) ∨ p5)) → p3) ∧ ((False → p1) ∧ p3)) → p1)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_556163283700689017149322344 : (((p2 ∧ (((p5 → ((p3 → p3) ∨ (p1 → (False ∨ (p5 → False))))) → p4) ∧ ((p1 ∨ p3) ∨ (p1 → (p1 → p3))))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203873908368335259000028002998 : ((p1 → ((p4 → (p1 ∧ p4)) ∧ p1)) ∧ ((((((p5 ∧ (True ∨ p3)) → (p1 ∧ False)) → False) ∨ ((p5 → True) ∨ True)) ∧ (p1 ∨ False)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230529629368779166575588751074 : (((False → False) ∧ p3) → ((((False ∧ (p3 ∧ True)) → p3) → (((((p1 → (p4 → False)) ∨ False) ∧ p5) ∧ (True ∨ (p1 ∧ p4))) ∨ p3)) ∨ True)) := by
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
theorem thm_5_vars_62215759510119975306271062373 : ((p3 ∧ ((p5 ∨ ((p4 → (False ∧ (True ∧ (((False ∧ ((p2 ∨ p2) → p5)) ∧ ((False ∨ False) ∨ False)) ∧ p1)))) ∨ (p3 → True))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60012758296634611330103719587 : (((p1 ∨ True) → (True → ((p3 ∨ ((((False ∧ p4) ∨ True) ∧ (p4 → (p2 ∧ False))) → ((((p1 → True) ∨ p5) ∨ p4) → p3))) ∨ True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741472552175283619554272645978 : ((((p5 ∨ p2) ∨ ((((p3 ∨ p5) ∨ (p4 ∧ p5)) ∨ True) ∨ (((p3 ∧ True) → ((p5 ∨ True) ∨ (p4 → (p3 → p1)))) → (False → p1)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137799903580371177058495434959 : ((p2 ∨ (p3 ∨ (((p4 → False) → p5) ∧ (True ∧ ((p3 ∧ p1) ∧ ((True ∨ p5) ∨ ((p5 → (p4 → p1)) ∧ p3))))))) ∨ ((False → p5) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149682628440297299123992512997 : ((p5 ∧ (((((False ∧ (p1 ∧ (True ∧ True))) ∧ (p1 ∨ p5)) → p3) ∨ ((p5 ∧ True) → (False ∨ p2))) → p5)) ∨ ((False → (p3 ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113789742967874886353218632456 : ((((p4 ∨ p5) ∧ (p4 → ((False → (p4 ∧ p1)) ∧ (False → (p5 ∧ ((p3 → p5) ∨ ((p4 ∧ p2) ∧ p5))))))) → (True → p5)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89108358253230772019876507425 : ((((False → p5) ∨ False) ∧ ((p5 ∧ (p3 → ((p3 ∨ p2) → p5))) ∧ ((p3 → (p4 → p4)) → (p2 → ((p5 ∨ (p1 ∧ p5)) → p3))))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57353098344443173845916278250 : (((p3 ∧ (p5 ∧ True)) ∨ ((True → (p2 → ((((True ∧ True) ∨ (p4 ∨ True)) → True) → (p2 → (p1 ∨ (p1 ∧ (p3 → p2))))))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615148595648760343779839862226 : ((((((((((((p3 ∨ p4) → False) → p4) ∨ p1) ∨ p3) ∨ p4) ∧ p3) ∨ (True → p5)) ∧ (True ∨ ((p3 ∧ False) → (p4 → p5)))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800434188241980024846256648876 : (((p2 → ((p5 ∨ (((((p4 ∨ p3) ∧ (((False → False) ∨ False) ∨ True)) ∨ p4) → (((p2 ∨ p1) ∧ p4) ∨ p3)) → (p1 ∨ p5))) ∨ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313081980356811299790720963754 : (p3 ∨ ((((((p3 ∨ p2) ∨ ((True → p4) → p5)) ∧ ((p5 ∧ (p2 ∧ ((False → True) ∧ (True ∧ p1)))) ∧ True)) → p5) ∨ (p1 → p5)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h3.left
      let h7 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h3.left
      let h18 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- One of the premise coincides with the conclusion.
      exact h19
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h3.left
    let h29 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h30 := h28.left
    let h31 := h28.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h31.left
    let h33 := h31.right
    -- Conjunctions on the left can always be decomposed.
    let h34 := h33.left
    let h35 := h33.right
    -- Conjunctions on the left can always be decomposed.
    let h36 := h35.left
    let h37 := h35.right
    -- One of the premise coincides with the conclusion.
    exact h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192859391739643368694006149069 : ((((p3 ∨ (p1 ∨ p2)) ∧ (p4 ∨ False)) ∧ (False ∨ p3)) → (p3 ∧ (((p1 ∨ ((p4 ∧ (p1 ∨ p1)) ∧ p4)) ∨ p3) → ((p1 ∧ p2) ∨ True)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h14 =>
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- One of the premise coincides with the conclusion.
          exact h15
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h19 =>
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- One of the premise coincides with the conclusion.
          exact h20
      case inr h21 =>
        -- False on the left can always be used.
        apply False.elim h21
  -- Implications on the right can always be decomposed.
  intro h22
  -- Disjunctions on the left can always be decomposed.
  cases h22
  case inl h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h1.left
      let h26 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h25.left
      let h28 := h25.right
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h26
          case inl h31 =>
            -- False on the left can always be used.
            apply False.elim h31
          case inr h32 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h33 =>
          -- False on the left can always be used.
          apply False.elim h33
      case inr h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- Disjunctions on the left can always be decomposed.
          cases h28
          case inl h36 =>
            -- Disjunctions on the left can always be decomposed.
            cases h26
            case inl h37 =>
              -- False on the left can always be used.
              apply False.elim h37
            case inr h38 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h39 =>
            -- False on the left can always be used.
            apply False.elim h39
        case inr h40 =>
          -- Disjunctions on the left can always be decomposed.
          cases h28
          case inl h41 =>
            -- Disjunctions on the left can always be decomposed.
            cases h26
            case inl h42 =>
              -- False on the left can always be used.
              apply False.elim h42
            case inr h43 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h44 =>
            -- False on the left can always be used.
            apply False.elim h44
    case inr h45 =>
      -- Conjunctions on the left can always be decomposed.
      let h46 := h45.left
      let h47 := h45.right
      -- Conjunctions on the left can always be decomposed.
      let h48 := h46.left
      let h49 := h46.right
      -- Disjunctions on the left can always be decomposed.
      cases h49
      case inl h50 =>
        -- Conjunctions on the left can always be decomposed.
        let h51 := h1.left
        let h52 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h53 := h51.left
        let h54 := h51.right
        -- Disjunctions on the left can always be decomposed.
        cases h53
        case inl h55 =>
          -- Disjunctions on the left can always be decomposed.
          cases h54
          case inl h56 =>
            -- Disjunctions on the left can always be decomposed.
            cases h52
            case inl h57 =>
              -- False on the left can always be used.
              apply False.elim h57
            case inr h58 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h59 =>
            -- False on the left can always be used.
            apply False.elim h59
        case inr h60 =>
          -- Disjunctions on the left can always be decomposed.
          cases h60
          case inl h61 =>
            -- Disjunctions on the left can always be decomposed.
            cases h54
            case inl h62 =>
              -- Disjunctions on the left can always be decomposed.
              cases h52
              case inl h63 =>
                -- False on the left can always be used.
                apply False.elim h63
              case inr h64 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
            case inr h65 =>
              -- False on the left can always be used.
              apply False.elim h65
          case inr h66 =>
            -- Disjunctions on the left can always be decomposed.
            cases h54
            case inl h67 =>
              -- Disjunctions on the left can always be decomposed.
              cases h52
              case inl h68 =>
                -- False on the left can always be used.
                apply False.elim h68
              case inr h69 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
            case inr h70 =>
              -- False on the left can always be used.
              apply False.elim h70
      case inr h71 =>
        -- Conjunctions on the left can always be decomposed.
        let h72 := h1.left
        let h73 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h74 := h72.left
        let h75 := h72.right
        -- Disjunctions on the left can always be decomposed.
        cases h74
        case inl h76 =>
          -- Disjunctions on the left can always be decomposed.
          cases h75
          case inl h77 =>
            -- Disjunctions on the left can always be decomposed.
            cases h73
            case inl h78 =>
              -- False on the left can always be used.
              apply False.elim h78
            case inr h79 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h80 =>
            -- False on the left can always be used.
            apply False.elim h80
        case inr h81 =>
          -- Disjunctions on the left can always be decomposed.
          cases h81
          case inl h82 =>
            -- Disjunctions on the left can always be decomposed.
            cases h75
            case inl h83 =>
              -- Disjunctions on the left can always be decomposed.
              cases h73
              case inl h84 =>
                -- False on the left can always be used.
                apply False.elim h84
              case inr h85 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
            case inr h86 =>
              -- False on the left can always be used.
              apply False.elim h86
          case inr h87 =>
            -- Disjunctions on the left can always be decomposed.
            cases h75
            case inl h88 =>
              -- Disjunctions on the left can always be decomposed.
              cases h73
              case inl h89 =>
                -- False on the left can always be used.
                apply False.elim h89
              case inr h90 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
            case inr h91 =>
              -- False on the left can always be used.
              apply False.elim h91
  case inr h92 =>
    -- Conjunctions on the left can always be decomposed.
    let h93 := h1.left
    let h94 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h95 := h93.left
    let h96 := h93.right
    -- Disjunctions on the left can always be decomposed.
    cases h95
    case inl h97 =>
      -- Disjunctions on the left can always be decomposed.
      cases h96
      case inl h98 =>
        -- Disjunctions on the left can always be decomposed.
        cases h94
        case inl h99 =>
          -- False on the left can always be used.
          apply False.elim h99
        case inr h100 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h101 =>
        -- False on the left can always be used.
        apply False.elim h101
    case inr h102 =>
      -- Disjunctions on the left can always be decomposed.
      cases h102
      case inl h103 =>
        -- Disjunctions on the left can always be decomposed.
        cases h96
        case inl h104 =>
          -- Disjunctions on the left can always be decomposed.
          cases h94
          case inl h105 =>
            -- False on the left can always be used.
            apply False.elim h105
          case inr h106 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h107 =>
          -- False on the left can always be used.
          apply False.elim h107
      case inr h108 =>
        -- Disjunctions on the left can always be decomposed.
        cases h96
        case inl h109 =>
          -- Disjunctions on the left can always be decomposed.
          cases h94
          case inl h110 =>
            -- False on the left can always be used.
            apply False.elim h110
          case inr h111 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h112 =>
          -- False on the left can always be used.
          apply False.elim h112



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135808603921223480794555507128 : (((p1 → (p2 ∧ ((p5 → p5) → ((((p3 ∨ p2) ∨ p4) ∧ p3) ∧ p1)))) → ((((p3 ∨ p3) → p3) ∨ p1) ∧ False)) ∨ ((False → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



