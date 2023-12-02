variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57395796656389978241264351251 : (((False ∨ (p2 ∧ p1)) ∨ ((True → p1) ∨ (((p5 ∧ False) → (((True ∨ p4) ∧ (False → ((p3 → p1) ∨ p5))) → p3)) ∧ (p1 ∨ True)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- False on the left can always be used.
    apply False.elim h10
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_457295148430081636422310791935 : (((((((p1 ∨ p3) ∨ (p5 ∧ p1)) ∧ (((p4 ∨ p5) ∨ False) ∧ (p4 → (True → p3)))) ∨ True) ∨ ((True ∨ False) ∨ ((p1 ∧ p4) → p5))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641074945306124581318988717320 : (((((p5 ∧ p2) ∨ ((((p4 ∧ (((p3 ∧ p3) → p4) ∨ p1)) → (p1 → (p5 ∧ (p3 ∧ (p1 ∧ p2))))) → (p4 → False)) ∧ p5)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659154975847771118109727212012 : ((((p3 → (((True → (p3 ∨ True)) ∨ (p1 → (p3 ∨ (False → p1)))) → ((p3 ∧ ((p4 ∧ p5) ∨ True)) ∧ (p1 → p5)))) ∨ (p3 → True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_357455775427551208507040798658 : (p5 → ((p1 → p3) → (((p2 ∨ (p3 ∨ ((True ∧ ((p3 ∨ p5) → False)) ∨ True))) ∨ p1) ∨ ((((p4 → (True → False)) ∨ p3) ∧ True) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244771293600856236711768125764 : ((p1 ∧ False) ∨ ((p4 ∨ p4) → (True ∧ ((p1 → (p1 ∧ p1)) ∧ ((p5 → ((((True ∨ p3) → False) ∧ p4) ∧ ((p3 ∨ False) ∨ p2))) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593412182808511378943752704366 : ((((((p2 ∧ (p4 ∨ ((False ∨ False) → (p1 → (p5 ∨ ((p4 → p4) → (True ∧ True))))))) → (p4 ∨ p2)) → ((p5 ∧ p4) ∧ False)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56347562469492225285719464424 : (((((True → p1) → p1) ∨ True) → ((p2 ∨ (True → ((p5 ∧ p2) ∨ True))) ∨ ((p4 ∧ (p3 ∨ p3)) ∨ (p1 ∨ ((p3 ∨ True) ∧ p1))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216538144531710148304171286591 : ((p5 → (p5 → (p3 ∧ p5))) ∨ (((((p2 → (((p3 → (False ∨ p4)) ∧ p5) ∨ (p2 → True))) ∨ (True ∧ p1)) ∧ p2) → p1) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159744486295127794821184006064 : (((((p1 ∨ (p4 → p3)) ∨ True) ∨ (False → ((p5 ∨ p2) → ((p4 ∨ p2) ∧ (p2 ∨ True))))) ∨ False) → ((p5 ∨ False) ∨ (False → (p5 ∨ p5)))) := by
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
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112562033051722792362857853079 : ((((p2 ∧ ((((False → (False ∨ (p3 ∨ (p4 → ((p5 ∨ p5) ∨ p3))))) ∧ (p5 ∨ p3)) ∨ (False ∨ p3)) → p5)) → p5) → p3) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134894358755712453595068039494 : (((p5 → ((False → ((p3 → ((p5 ∧ (p3 → p3)) ∨ ((False ∨ (p1 ∨ p3)) → p4))) → False)) ∧ (p4 ∨ p3))) → p1) ∨ ((False → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51918452867535383864959008134 : ((((((p2 ∧ p2) ∨ (False ∨ p4)) ∨ (((False ∧ p3) ∨ True) → p3)) → (p4 ∧ p1)) ∨ ((((p4 → (p1 → p5)) ∧ p5) ∧ p2) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191888378737704945452410222556 : ((p5 ∨ (((((p4 → p3) ∧ p4) → p1) ∧ p3) ∧ False)) ∨ (p3 → ((p3 ∨ p3) ∧ ((p3 ∧ (p1 ∧ (((p3 ∧ p4) → p1) ∨ p4))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692116858384755376909368021255 : (((((p4 ∨ (((p4 → (p3 ∧ False)) ∧ (p3 ∧ (False → p3))) ∨ p1)) ∧ p3) ∧ ((((False ∨ (False → p4)) ∨ (p2 ∧ p2)) ∧ p1) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_820834291500064911012847242136 : ((((((((p2 ∧ (p4 ∧ True)) ∧ True) → ((p2 ∨ (False → p2)) ∧ (p5 ∨ p2))) → False) ∧ ((p3 ∨ p4) ∧ (p4 → (p1 ∨ p4)))) ∧ p3) → p5) ∧ True) := by
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
  cases h6
  case inl h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : (((p2 ∧ (p4 ∧ True)) ∧ True) → ((p2 ∨ (False → p2)) ∧ (p5 ∨ p2))) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
      -- Conjunctions on the left can always be decomposed.
      let h17 := h10.left
      let h18 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h23 := h4 h9
    -- False on the left can always be used.
    apply False.elim h23
  case inr h24 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h25 : (((p2 ∧ (p4 ∧ True)) ∧ True) → ((p2 ∨ (False → p2)) ∧ (p5 ∨ p2))) := by
      -- Implications on the right can always be decomposed.
      intro h26
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h27.left
      let h30 := h27.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h29
      -- Conjunctions on the left can always be decomposed.
      let h33 := h26.left
      let h34 := h26.right
      -- Conjunctions on the left can always be decomposed.
      let h35 := h33.left
      let h36 := h33.right
      -- Conjunctions on the left can always be decomposed.
      let h37 := h36.left
      let h38 := h36.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h35
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h39 := h4 h25
    -- False on the left can always be used.
    apply False.elim h39
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257184397806395960341661444339 : ((p2 ∨ p2) → ((((p4 ∨ (((((p2 ∧ p3) → ((p5 → (p5 ∧ False)) → p1)) → (True ∧ p4)) ∨ (p5 ∨ p1)) → p4)) ∨ True) → p1) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71007161276140171285270954928 : (((((p1 ∨ (p1 ∧ (True → (p1 ∧ False)))) ∨ True) → (((((p5 ∨ (False ∨ True)) → p2) ∨ (p3 → p5)) ∧ (p5 ∧ False)) ∨ p5)) ∧ p2) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p1 ∨ (p1 ∧ (True → (p1 ∧ False)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
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
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h8.left
      let h14 := h8.right
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141046039298333907805284768039 : (((p3 → ((False → False) ∧ (p5 ∧ (False ∨ p3)))) ∧ ((((p5 ∨ (True → p4)) ∨ (p5 → (p3 ∧ False))) ∧ p4) → False)) → (p4 → (p3 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (((p5 ∨ (True → p4)) ∨ (p5 → (p3 ∧ False))) ∧ p4) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187628726836257243502479424238 : ((p5 ∨ ((False ∧ ((p2 → (True → p4)) ∧ (False ∨ p1))) ∨ p3)) → ((False ∨ (p3 ∨ ((p4 ∨ (True → p2)) → p2))) ∨ ((False → p3) → p5))) := by
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
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733220963727576296822207261211 : ((((p3 ∧ p2) ∧ (True → (((p2 → (p3 → (True ∧ (p4 ∧ ((p1 → p5) ∧ (p3 ∨ True)))))) ∨ p2) ∨ ((p4 → p3) ∨ (False ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196781893537192426278292399973 : ((((p2 ∨ p1) ∧ (p2 ∧ (p2 → p4))) ∧ True) ∨ (((p2 ∨ (True → ((True → p3) ∨ ((p4 ∧ p2) ∨ p3)))) → ((p1 ∨ p2) ∨ True)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218779957509767686384837111165 : ((p1 ∧ ((p5 ∧ False) → p4)) → ((p4 → (p2 ∧ ((((p2 ∧ (p5 ∧ p2)) ∨ False) → p5) ∧ (((p4 → p5) ∨ (p1 → p1)) ∨ p2)))) ∨ True)) := by
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
theorem thm_5_vars_165201240691906539604113416787 : ((((p1 ∨ ((p3 → ((p3 ∧ ((True ∧ p3) → p2)) ∧ True)) → False)) ∨ p4) ∨ (True ∧ p4)) ∨ ((p3 ∧ p2) → (p3 → ((p5 ∧ p4) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47596297701768370435495370056 : (((p3 → ((p3 ∨ (((((p5 ∧ (p1 ∨ p5)) ∨ (p4 ∧ p2)) ∨ (p4 ∨ p5)) → False) → (True → (p4 ∨ False)))) → p1)) ∨ (p3 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116096442227721013529493450412 : ((((p2 → p2) ∨ False) ∧ (((True → p5) ∨ ((False ∨ p5) ∧ (((p2 ∨ False) → ((p5 ∨ (False → p4)) → False)) → p1))) → p1)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301292461746441995288595708471 : (False ∨ (((p1 ∧ p3) ∧ ((True ∧ p4) → p5)) → ((((p4 ∧ p5) ∨ False) ∨ True) ∧ (((p5 → p4) ∧ ((False ∧ p2) → True)) ∨ (p4 → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h10
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720494473641652132604672901879 : (((((p3 ∨ (p4 ∧ p3)) ∨ p1) → (((p3 → (p1 ∨ (False → (p5 ∨ (True ∨ p4))))) → p5) → ((False ∧ p2) ∨ ((True ∧ p1) ∨ p3)))) ∨ p4) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149579442941104302046297539877 : ((p3 ∧ ((((p4 ∨ (p2 ∨ False)) → (p3 ∨ (p4 ∨ ((p1 ∨ p4) ∧ (p3 ∧ (p4 ∧ p4)))))) → False) ∧ True)) ∨ (True ∨ ((False ∨ p2) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49308279141501706650606644210 : (((p1 ∨ ((p3 → p5) ∨ (p5 ∧ (((p3 ∨ (False ∧ p4)) ∨ ((p5 ∧ (False ∧ p4)) ∨ (p4 → False))) ∨ p5)))) ∨ (p1 ∨ (False → p4))) ∨ p1) := by
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
theorem thm_5_vars_212753801966338431312053431840 : ((p1 → ((p3 ∨ True) ∨ True)) ∧ (p2 ∨ ((((p5 ∧ p5) → ((((p4 → ((p2 ∧ p1) → False)) ∨ True) → p2) ∨ p3)) ∨ (p5 → True)) ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616722349491933217942341210964 : ((((((p5 ∨ (p2 ∧ ((p2 → p5) → (True ∧ p4)))) → False) ∨ (False ∨ (((p5 ∧ True) ∧ ((False ∧ (p1 → p2)) ∧ p5)) → p3))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_59160547470166419300531000374 : (((False ∨ p2) ∨ ((True ∨ ((((p3 → ((p2 → p3) ∧ (p5 → (p3 ∧ (p4 ∨ p1))))) ∧ p1) → (False ∧ p5)) → p1)) → (False ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193037884518209795682303044987 : (((p5 ∧ ((p1 ∧ (p3 ∧ p4)) → True)) → (True ∨ True)) → ((p2 ∨ p4) ∨ ((p5 ∧ (True ∧ ((((False ∨ p5) ∧ p1) ∨ True) → False))) → p4))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (((False ∨ p5) ∧ p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19560997108920054707887746030 : ((((((p3 → ((p4 ∧ (False ∧ p5)) ∧ False)) ∨ p4) ∨ p1) ∧ (p1 ∨ (True → p3))) ∨ (p2 ∨ ((p3 ∧ (p4 → p1)) → (False ∨ True)))) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60107061832015808005766107787 : (((p3 ∨ p2) → ((p1 ∨ p5) ∨ (((p4 ∨ (((True → False) → (p1 ∧ p3)) → p1)) ∧ (p1 ∧ (p4 ∨ p5))) ∨ (False ∨ (False ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125544915541326744028592762461 : (((False → p1) ∧ ((((((True ∧ p2) ∧ True) ∨ p3) → ((p5 → p5) → (False ∨ True))) ∧ (((p5 → True) → p4) → True)) ∨ p2)) → (p4 → p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178520530317510524417710569507 : ((((False ∨ ((p5 ∨ (p2 ∨ p4)) ∨ True)) → p3) → (True → (p2 ∧ p2))) ∨ ((True ∧ (p4 → p3)) → (((True ∧ False) → (p2 → True)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344287030955982170045977102580 : (p2 → (p3 ∨ (((((p3 ∨ True) ∧ ((p5 ∨ (p1 ∧ True)) ∨ (False ∧ True))) ∧ (((False ∧ p3) → False) ∧ p3)) → (False ∧ (p4 → p5))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310071839044232182274841095843 : (p2 ∨ ((p2 ∧ ((p4 → p1) ∧ (((False ∧ p3) ∨ (((p3 ∧ p5) ∧ True) → p1)) ∧ p5))) → (((p2 ∨ True) → (p1 ∨ p5)) ∨ (True ∨ True)))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632426089119587461631735640488 : (((((p1 ∨ (((((p1 ∨ (False → (True ∨ (p5 ∨ p4)))) → p2) → ((p2 ∧ p4) ∨ ((p2 ∧ p5) ∨ p1))) → p5) ∨ p5)) → True) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205165128288241493588982239092 : (((p4 ∧ (p1 ∨ p4)) ∧ (False ∨ False)) ∨ (((p1 → (p5 ∨ p2)) ∨ True) → ((True ∨ (p2 → False)) ∨ (((p2 ∧ p2) ∨ p5) ∨ (p5 ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233175699856449975417756165501 : ((p5 ∧ (p2 ∨ False)) → ((((p1 ∨ ((True → (p5 ∨ False)) ∨ (p4 ∧ True))) ∨ (p2 ∨ p5)) → ((p3 ∧ (False → (True ∨ p1))) ∨ p2)) ∨ p4)) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h16 =>
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119437835504759821053711200872 : ((p4 → ((((p4 ∨ (p1 ∨ False)) → (p3 ∨ (p1 ∧ p2))) ∧ ((p5 → p2) ∨ (p1 ∧ p1))) → (((p1 ∧ p1) → p5) → p5))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615200127754471283454728866645 : ((((((p1 → (True ∧ True)) → (p1 ∨ ((p3 ∨ (p2 ∨ (p5 ∧ False))) ∧ (True ∨ p1)))) ∧ ((True ∨ (p3 ∧ True)) ∨ (True ∨ p1))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172283730152348576273477985952 : (((p1 ∨ (((p4 → p1) ∨ p2) ∨ (p5 ∧ p2))) ∨ (p3 → (p5 ∨ (p5 → p5)))) ∨ (((p4 → p1) → ((True ∨ True) ∧ (p2 → p1))) ∨ p1)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40849680437497143221550480295 : ((((((((p3 ∨ (p5 ∧ (((p2 ∧ (p2 → (False ∧ p5))) → True) ∨ p2))) ∧ (p1 → p4)) ∧ p2) → p3) ∧ p3) ∧ (p2 ∨ p4)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40335742281073842583228084422 : ((((((p1 ∨ (((((p4 ∧ p4) ∨ True) → False) → p3) ∧ True)) → ((True ∨ (p3 → (p5 ∨ False))) → (True ∧ p1))) ∨ True) ∨ False) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50210059720658534131718729823 : (((((((p1 ∨ ((p3 ∧ p5) → (False ∧ (p5 → p4)))) → p3) ∨ (p2 ∧ p4)) ∨ (p5 ∧ p2)) ∨ True) ∨ (False ∨ (True ∨ (True ∧ p1)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709646553358430241238107555566 : ((((p3 ∨ (p1 ∧ ((False ∧ p3) ∨ (p2 → p3)))) → (((p3 ∧ True) ∧ (True ∧ ((((True → True) ∧ False) → (p5 → False)) ∧ True))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180179863253245098848467856621 : (((((p2 → (p3 ∧ p1)) → p2) ∧ (p5 ∨ (p3 ∧ (p2 → p2)))) → p5) → (p3 ∨ ((((((True ∧ p3) ∧ True) ∧ p5) ∧ True) → p3) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64404482393763044797901562128 : ((p1 ∨ (((p5 ∨ ((p1 ∧ (True ∧ p4)) ∨ (False ∨ (True ∧ True)))) ∨ (p5 → (p2 → (p2 → ((True → (p5 → p4)) ∧ p4))))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247358560195906316340645157277 : ((False ∨ p1) ∨ ((((p2 → p4) ∧ ((p5 ∨ (p4 ∨ ((p3 ∨ False) → (p3 ∧ True)))) → p4)) → ((p5 ∨ (p4 ∨ p3)) ∨ p1)) ∨ (p2 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∨ (p4 ∨ ((p3 ∨ False) → (p3 ∧ True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741790914813873549184354647174 : ((((True → p3) ∨ ((p2 ∧ (False → p3)) → ((p5 ∨ (((p3 ∨ p1) ∨ p3) → p5)) → (p2 ∧ ((False → (True → p2)) ∧ (p3 → p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165807568564981927910194580278 : ((((p3 ∧ True) → p5) ∧ ((p3 → (((((p4 ∨ p5) → p3) ∨ p2) → p4) → p1)) → False)) ∨ (((p1 → p5) ∨ ((p3 ∧ False) → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319556366776233775403582379998 : (p4 ∨ ((p4 ∧ ((True ∧ (p5 ∧ (True ∧ (p1 ∧ True)))) ∧ p1)) ∨ (p4 ∨ ((p2 ∧ True) → (((p5 → p5) ∨ (p3 ∨ False)) ∧ (p2 ∨ p5)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199382559433414804361068667982 : (((((False ∨ p2) ∨ False) → (True → p2)) ∨ p5) → ((False → (p4 ∧ (p5 ∨ (True → True)))) ∧ (False ∨ ((((False ∨ p5) ∧ p5) ∨ p2) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320367978263783896380690762889 : (p4 ∨ ((p4 → False) ∨ (True ∧ (False ∨ (((p1 ∧ (((p1 ∨ ((True ∧ p5) ∧ (p4 ∨ (p5 ∨ p4)))) ∨ False) ∧ p1)) ∨ True) ∨ (p4 ∧ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_340849008139908778806111467097 : (p2 → (((((True → ((p2 → (p4 ∨ p2)) → False)) ∧ True) ∨ (p1 ∧ ((p2 → (p2 → (p2 ∨ p4))) ∧ p4))) ∨ (p2 ∨ (p5 ∧ p5))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68308543403500255635488569482 : ((p3 → (((p4 → (((p4 → False) ∧ False) ∨ False)) ∨ (p2 ∧ (p1 ∧ (p2 ∨ ((True ∧ p2) → p4))))) ∨ (p3 ∨ ((p4 ∨ True) → p1)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68557880073105315805941792715 : ((p4 → ((((((p4 ∧ True) ∧ ((p1 → ((p4 ∨ p4) ∨ (p5 ∧ p2))) ∨ p4)) ∨ (p3 ∨ ((False ∧ p5) → p3))) → p1) ∧ False) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49441361185776866111404343928 : ((((((p1 ∧ (True ∨ (p4 → True))) ∨ ((p3 → p4) ∨ (p3 ∨ False))) ∨ (p5 ∨ (p5 → (False ∨ True)))) ∨ p2) → ((p3 ∨ p4) ∨ True)) ∨ False) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h5 := h4.left
        let h6 := h4.right
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h13 =>
            -- False on the left can always be used.
            apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766736357251503947889931674968 : (((p4 ∧ (p1 ∨ (p3 ∧ (((p2 ∧ p4) ∨ True) → (((p5 ∨ ((((True ∧ ((p3 → True) ∧ p2)) ∧ True) → False) ∨ True)) ∧ p4) ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124726385038257772218372916024 : ((((True → (p5 ∧ False)) ∨ False) ∧ ((p1 ∨ False) → (True ∨ ((p3 → (True → False)) → ((p4 ∧ p1) → (p3 ∧ (p4 → p1))))))) → (False ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
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
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622497038094866842966883509398 : ((((p3 ∧ (p2 ∨ ((((((p3 ∧ True) ∧ False) ∨ ((p1 ∨ True) ∧ p4)) ∧ (p1 → (True ∧ p2))) ∧ (p1 → (p2 → False))) ∨ True))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253774728296994993721347585579 : ((p1 ∧ p1) → (p3 → (((p2 ∨ ((p4 → (p3 → (p1 ∨ p4))) ∨ False)) ∧ ((False ∨ True) → p4)) → (False ∨ (p1 ∧ ((p4 ∨ p5) ∨ p1)))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h1.left
      let h12 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h12
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768016396140380990736997601066 : (((p5 ∧ ((((True ∧ p4) ∧ (p3 ∨ ((((p2 ∧ True) → p1) ∨ ((True ∧ (p3 → True)) → p3)) → (p2 → True)))) ∨ p4) ∧ (p2 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42942928139271825554817058897 : (((p4 → (((p2 → p3) ∨ False) ∨ ((True ∧ (((p2 ∨ ((p3 ∧ (p2 ∧ (p3 → (p3 ∨ p3)))) ∨ p5)) ∨ p3) ∧ p1)) ∨ p5))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234436094235181463808871698077 : ((p2 → (p2 ∧ p1)) → (((p3 ∨ (False ∨ p2)) → (((False ∨ (((p1 ∨ p4) ∧ (True → (p1 ∨ True))) ∧ p5)) ∨ (False → p4)) ∨ False)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681335062608443852615010075141 : ((((False ∨ (((True → p5) ∨ (p4 ∧ p4)) ∧ (p5 → (True ∧ (((p1 → p2) → (p1 → p3)) ∧ True))))) → ((p5 → (p4 ∧ p1)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312359998701966162880502294967 : (p2 ∨ (p3 → (((((((p2 ∨ p1) → p5) → p2) ∧ (p1 ∧ (True ∨ (p2 ∧ (((True ∧ p5) ∨ p4) ∨ True))))) ∨ p3) ∨ p2) ∧ (p4 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156416530686372402249872783453 : ((p1 → ((((p3 ∧ p4) ∧ ((False ∧ False) ∧ (p3 ∧ ((p2 → True) → p5)))) ∧ p5) ∨ (p2 → True))) ∧ (((True ∧ p3) → (False ∨ p3)) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117007436250413045195897879344 : (((False ∨ p3) → ((p5 ∧ p3) → (((True ∧ ((False ∨ p5) → True)) ∧ (True ∨ False)) → (p2 → (((p1 → p2) → p4) ∧ True))))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354852858244951490466675409312 : (p5 → (((p4 → p2) ∨ ((((True ∧ (((p1 ∧ ((p3 ∧ p3) → True)) ∨ (((p1 ∨ p4) ∧ p2) ∧ p4)) ∧ p3)) ∧ p5) ∨ True) ∧ p5)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611979708775052517627618983316 : (((((((((p5 ∧ p3) → (p2 → p5)) → p2) → (((p1 ∧ p5) → (p1 ∧ p3)) ∨ (p4 → (p1 ∧ p3)))) ∨ True) ∧ (p2 ∨ p2)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_151414143301337719901512547900 : ((((False → p4) ∧ ((True → p5) ∧ (((p2 ∨ p1) → True) ∧ (p3 ∧ (p1 → (p5 ∨ p3)))))) ∧ (p5 ∨ p3)) → (((p4 ∨ True) ∨ True) ∨ p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644011030128264933027232840837 : ((((True ∨ ((((((p2 ∧ p3) ∨ (True ∨ (False ∧ True))) → p3) ∨ (((False → p2) ∧ p4) → (p1 ∨ p1))) ∨ p3) → (p1 ∧ True))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57987271373332815277596306341 : (((p4 → (p2 → p1)) → ((p2 ∨ True) ∧ (p3 → ((p2 ∨ ((p3 → True) ∧ (False ∨ ((True ∨ (p4 ∧ p3)) ∨ p3)))) ∧ (p1 → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62336274334582654219400782349 : ((p3 ∧ ((p2 ∧ ((((p1 ∨ (((p4 → ((p4 → p1) ∧ p5)) → True) ∨ True)) ∨ (p1 ∧ False)) ∨ p2) ∧ p3)) ∧ ((True ∨ p1) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317862689004253826483965405652 : (p4 ∨ (((False ∨ p1) ∨ (p2 ∧ (((p4 ∨ True) → p5) ∨ (((p5 → (((p5 ∧ (False ∨ p5)) ∧ p5) → p1)) ∧ (False ∧ p1)) ∨ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115870671243179402758528120343 : (((((p2 ∨ p2) ∧ p1) ∧ p4) ∨ ((((p3 ∨ p4) → (p2 ∧ True)) ∧ True) ∨ ((False ∨ p1) ∨ (((p2 ∨ p3) ∧ p3) ∨ False)))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116153269944940653402231742790 : (((p2 ∨ (False ∧ p1)) ∧ (((p2 ∨ p3) ∨ (((p4 ∧ p5) ∨ ((p2 → p4) → (p1 ∧ True))) ∧ ((p1 → p1) → True))) → False)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135516164590163597559411785175 : ((((((p1 → (p3 → (p3 ∧ p3))) ∨ (p1 → ((p5 ∨ False) ∧ False))) ∨ p1) ∧ False) ∧ ((p5 ∨ p5) ∧ (p5 ∨ p2))) ∨ ((p2 → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47573890232082482333780108683 : (((p1 → (((((p4 → True) ∨ (p2 ∨ p5)) → False) ∧ ((p4 ∧ True) → (((p1 ∧ p1) → p2) ∧ (False → p1)))) → p5)) ∨ (False → p3)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345674510276612782244931368960 : (p3 → ((p1 ∨ (p1 → ((p1 ∧ (p3 ∧ p5)) ∧ ((p3 → p3) → ((((False ∨ p4) ∨ (False → True)) ∨ False) ∧ ((p5 → p1) ∧ p4)))))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627368813770504920192079654856 : ((((((((((p2 ∨ p4) ∨ p3) ∧ p1) → (p2 ∨ (False ∧ (((p5 ∧ p5) ∧ p1) ∧ (p5 ∧ True))))) → (p3 ∧ p5)) → p4) ∧ p5) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226032959719252642145955632742 : (((p4 ∧ p5) ∨ p5) ∨ (((((((p2 → True) → False) ∧ False) → p4) ∧ p2) ∨ (((p1 ∨ p4) → p3) → p3)) ∨ (False → (p5 → (True ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134564621837570963384111531529 : ((((p2 → (True ∧ ((((((p1 ∧ False) ∨ p3) ∨ p1) ∧ (p3 ∧ (True → (p5 ∨ p5)))) ∧ True) ∧ p4))) → p1) → False) ∨ ((True ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258246097110391732314771401981 : ((p4 ∨ p5) → (((False ∨ (p1 ∨ False)) → p5) → ((((p4 → p1) ∧ (p5 ∧ p4)) ∧ ((True ∧ p3) ∧ (p2 ∨ ((p2 ∨ p1) → p3)))) ∨ True))) := by
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
theorem thm_5_vars_234192956746783957021473898943 : ((False → (p1 ∧ True)) → ((p5 → (((((True ∨ p1) → p3) → p4) ∧ p3) ∧ (False → True))) ∨ ((p5 ∧ (p3 ∧ p1)) → (p3 → (True ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165702730876419496513194315136 : ((((p2 ∧ (p3 ∧ p2)) ∧ True) ∧ ((p1 ∨ (True ∨ p5)) ∧ ((p4 ∨ (p3 ∨ False)) ∨ p2))) ∨ (((((True → p3) ∧ False) ∨ p4) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592037363320743251778942295304 : (((((p4 ∧ ((p4 ∧ (((p4 ∨ ((False → p3) ∨ (p4 ∨ p2))) ∨ (False ∨ (True → p3))) ∨ p3)) ∨ (True → p4))) ∨ (p2 ∧ p1)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171799851256899790884960924111 : ((((((p1 ∧ ((p1 ∨ p5) → p5)) ∨ p3) → p1) ∨ (True ∧ (False → p1))) → p1) ∨ (p1 → (p5 → ((((p5 ∨ p1) ∨ p4) ∧ p5) → p5)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85095612866257356550614775550 : (((((True ∨ (p3 → (p1 → ((p4 ∧ (p3 ∨ p5)) → p5)))) ∨ p5) ∨ p2) → (((p3 ∨ ((False ∧ (p5 → p1)) → p4)) ∧ p5) ∧ p3)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True ∨ (p3 → (p1 → ((p4 ∧ (p3 ∨ p5)) → p5)))) ∨ p5) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
theorem thm_5_vars_201075891777286431128117730319 : ((p5 ∨ ((True ∧ p3) ∨ (True → (True → p3)))) → ((((((p4 ∧ p5) ∨ p1) → True) ∨ (p1 ∧ p5)) → (p3 → p1)) → ((p5 ∨ p3) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h10 := h8 h9
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h12 := h10 h11
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305497299735877461592993657387 : (p1 ∨ (((p3 ∧ ((((p2 ∨ p3) → p5) ∨ (True ∧ p4)) ∧ True)) ∨ (p3 ∧ False)) ∨ ((((((p3 → p1) ∨ True) ∧ False) ∧ p5) ∨ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354611556131444006629783670654 : (p5 → (((((True ∨ p2) ∧ ((((((p2 ∨ (False ∧ p4)) ∧ True) ∨ p4) ∨ (True → p1)) ∧ True) ∨ p3)) ∧ ((False ∨ False) → p5)) ∨ p5) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321595144206076110927002654948 : (p4 ∨ (p3 → (((p4 ∨ (p2 ∨ ((p2 ∨ p4) ∨ (((True ∧ (p3 ∧ p3)) → (p4 ∧ p2)) → ((p4 → p3) ∧ (True ∨ p2)))))) ∧ p3) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166127459375738072816886198145 : ((True ∧ (((((True ∨ p3) → p2) ∨ (False → p1)) ∨ (False ∨ p4)) → ((p2 ∨ True) → p4))) ∨ (((p3 ∧ False) → (False ∧ (p5 ∧ False))) ∨ p4)) := by
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
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171292951225500863621416440814 : ((((((False → ((p2 ∧ ((p5 → False) → False)) ∧ p4)) → False) ∧ p2) ∧ p1) ∧ p5) ∨ ((p5 ∧ p1) → ((p3 ∨ p4) ∨ (False → (p3 ∨ p3))))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



