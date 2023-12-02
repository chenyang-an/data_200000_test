variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_941940247279200531142145709127 : ((((((True → p1) ∧ p3) ∧ p5) ∧ (((p1 → (p2 → (((p5 → ((((p1 ∧ p4) ∧ False) → p2) ∧ False)) ∧ p4) → False))) ∨ False) → False)) → False) ∧ True) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h8 : ((p1 → (p2 → (((p5 → ((((p1 ∧ p4) ∧ False) → p2) ∧ False)) ∧ p4) → False))) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h14 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h15 := h12 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- False on the left can always be used.
    apply False.elim h16
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h17 := h3 h8
  -- False on the left can always be used.
  apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122844358641313132660306836878 : (((((False → p5) → (False → (((((False → p5) ∨ p1) → (p2 ∧ True)) → p2) ∨ p4))) → (False ∧ p1)) ∧ ((p1 ∧ p2) ∨ p2)) → (p5 ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : ((False → p5) → (False → (((((False → p5) ∨ p1) → (p2 ∧ True)) → p2) ∨ p4))) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h7
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : ((False → p5) → (False → (((((False → p5) ∨ p1) → (p2 ∧ True)) → p2) ∨ p4))) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- False on the left can always be used.
      apply False.elim h15
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h16 := h2 h13
    -- We need to get the left conjuct of h16 based on <expert-advice>.
    let h17 := h16.left
    -- False on the left can always be used.
    apply False.elim h17
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h23 : ((False → p5) → (False → (((((False → p5) ∨ p1) → (p2 ∧ True)) → p2) ∨ p4))) := by
      -- Implications on the right can always be decomposed.
      intro h24
      -- Implications on the right can always be decomposed.
      intro h25
      -- False on the left can always be used.
      apply False.elim h25
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h26 := h18 h23
    -- We need to get the left conjuct of h26 based on <expert-advice>.
    let h27 := h26.left
    -- False on the left can always be used.
    apply False.elim h27
  case inr h28 =>
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h29 : ((False → p5) → (False → (((((False → p5) ∨ p1) → (p2 ∧ True)) → p2) ∨ p4))) := by
      -- Implications on the right can always be decomposed.
      intro h30
      -- Implications on the right can always be decomposed.
      intro h31
      -- False on the left can always be used.
      apply False.elim h31
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h32 := h18 h29
    -- We need to get the left conjuct of h32 based on <expert-advice>.
    let h33 := h32.left
    -- False on the left can always be used.
    apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63938046064422577874410587302 : ((False ∨ (((p4 ∧ ((False ∨ (p3 ∨ p2)) ∨ ((((p1 ∧ p4) ∧ p5) → p4) → True))) ∨ (False → (p3 ∧ (p2 ∧ (p2 → p3))))) ∨ p1)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179331826532814950051003680956 : ((p1 ∨ (((p3 ∧ False) ∨ (((p4 ∨ p3) ∨ p4) ∧ p1)) ∨ (p5 ∧ False))) ∨ (False → ((p4 ∨ ((True ∧ p5) ∧ p1)) ∧ (p3 ∨ (True ∧ p4))))) := by
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
theorem thm_5_vars_710097250799551098261891437954 : (((((p5 → ((False ∨ False) → p1)) ∧ p4) ∧ ((p4 ∨ False) ∧ ((((True ∧ True) → True) → ((True ∨ ((False ∨ p2) ∧ p1)) ∧ p1)) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208835397390286619006673389470 : ((p3 ∧ (p5 ∧ ((False ∨ False) → p1))) → ((p1 ∨ (False ∨ p1)) ∨ (((p5 ∧ p2) ∨ (True → (p5 ∨ p2))) ∨ ((p2 ∨ (p1 ∨ p2)) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349274621068220229203647771786 : (p3 → (p2 → (((True → ((((((p1 ∧ (p2 ∧ (False → p3))) ∧ p4) ∧ False) ∧ p2) ∨ p1) ∨ p4)) ∨ (p2 ∧ ((p3 → p3) ∨ False))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312127517268307054666583285292 : (p2 ∨ (True → (((((p5 ∧ p5) → p3) ∨ True) ∨ (p3 ∨ (p3 ∨ ((p1 ∨ (p2 ∧ p3)) ∨ p2)))) → (((p1 → p2) → False) → (False ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
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
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h14 =>
            -- Conjunctions on the left can always be decomposed.
            let h15 := h14.left
            let h16 := h14.right
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
theorem thm_5_vars_42964414116194530467279970119 : (((p5 → ((True ∧ (True ∧ (p1 ∧ (((p2 ∨ ((p4 ∨ p4) ∨ (((p4 → p5) → p2) ∨ (p4 ∧ True)))) → p4) ∧ p1)))) ∨ p5)) ∨ p5) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115421420926915939155043049276 : ((((p2 ∨ ((p5 ∨ True) ∧ (p1 ∨ p5))) ∧ True) ∨ (((False ∨ ((((p2 ∧ p3) → False) → p5) ∨ (p4 → p5))) ∧ p2) ∨ True)) ∨ (p3 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109228382797636832854377002474 : ((False ∨ ((p1 → ((False ∧ p1) → True)) ∧ ((p3 ∨ ((((p1 ∨ (p4 ∧ p4)) ∨ (p5 ∨ (False → p3))) → p4) ∧ p5)) ∨ True))) ∧ (False → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149015897070111387419465533178 : ((((p1 ∨ False) ∨ p3) ∨ ((((p2 ∨ True) ∧ p1) ∧ (True ∨ (True ∨ ((p1 → p2) ∨ p2)))) ∨ (p1 ∨ p1))) ∨ (p3 ∨ (p3 → (p5 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230708781780803093755568758058 : (((p4 → p4) ∧ p2) → ((p4 ∧ (False ∧ ((False ∨ ((p2 → ((p5 ∧ False) ∧ ((((p5 ∧ False) → False) ∨ p2) ∧ p1))) ∨ p2)) ∧ True))) ∨ True)) := by
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
theorem thm_5_vars_208879963221589679915638562356 : ((p4 ∧ (p2 ∧ (p5 → (True ∧ p3)))) → ((p2 → (p1 ∧ ((False ∨ p5) ∧ ((p2 → p5) ∧ ((p1 → p3) → (p2 ∧ (p4 ∨ False))))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157674383077904155604500855081 : (((((p5 ∧ True) ∧ True) → ((((p1 → (p2 ∧ p4)) → p3) ∧ p1) ∨ p1)) ∨ (p1 ∧ (p1 ∧ False))) ∨ ((p3 ∧ ((p4 ∧ p4) ∧ p2)) → p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62920238564861271714828258754 : ((p4 ∧ (False ∧ ((((p3 ∨ p3) → (p5 → p1)) ∧ (((True → (p5 ∨ True)) ∨ ((p2 → p4) → True)) ∨ p3)) ∧ (False ∨ (p2 ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51920814355165445194574340914 : ((((p2 ∨ (p3 → ((p2 → p3) ∧ ((p3 ∧ p4) → (p4 ∨ p5))))) → (p5 ∧ True)) ∨ ((((True ∧ (p4 ∧ p5)) ∨ p3) ∧ p4) → p4)) ∨ p5) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760200063691985094684149758751 : (((p2 ∧ ((False ∨ p3) ∧ ((p1 ∨ (((((((True ∨ True) ∨ False) → p4) ∨ (p1 ∧ p4)) ∧ p3) ∨ p2) ∧ True)) ∧ ((p5 ∧ p1) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217773660602566489300156813536 : (((p5 ∧ (p5 → p4)) → p5) → (True ∧ ((False ∨ (((p5 ∧ True) ∨ (p2 ∧ p2)) ∧ (p3 ∨ (p5 ∨ p5)))) → (p4 → ((p2 ∨ p3) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h11 =>
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
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
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
theorem thm_5_vars_60199511346165465175470264575 : (((p5 ∨ p5) → (((((((p1 ∨ (p3 ∧ p2)) → (True ∨ True)) → p4) ∧ (p4 ∨ p5)) ∧ (p4 ∧ (False ∧ p5))) ∧ (True → p5)) ∨ p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_325004621167149958119023777734 : (p5 ∨ ((True ∧ p3) → ((p3 ∨ p5) ∧ ((((p1 → p4) → (((p3 → True) ∧ (p5 → True)) → (p4 ∨ (False → p4)))) ∧ (False → p2)) ∧ True)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h10
  -- False on the left can always be used.
  apply False.elim h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138424360359849812878412591158 : ((p5 → ((((p4 → p1) → (((p3 ∧ p4) → (True → (((False ∨ p2) ∨ True) ∧ p4))) ∨ p2)) → p4) ∨ (p1 ∨ p2))) ∨ (p2 ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53491796470956800756457816078 : (((True ∨ ((((False ∨ (False → p1)) ∨ (p2 ∧ True)) ∨ p4) ∧ p2)) → ((p2 → p4) ∨ (False → ((p2 → ((p2 → p2) → True)) ∨ p1)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- False on the left can always be used.
          apply False.elim h9
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h11
          -- False on the left can always be used.
          apply False.elim h11
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_877811878601783073547207935683 : (((((False ∨ (True ∧ True)) ∧ ((p5 ∧ p2) ∧ (p1 ∨ (p2 → ((p4 ∨ (p2 ∧ (p5 ∧ p2))) ∧ ((p4 → p2) ∧ False)))))) ∧ (True → p5)) → p1) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h5.left
    let h11 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h16 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h17 := h15 h16
      -- We need to get the right conjuct of h17 based on <expert-advice>.
      let h18 := h17.right
      -- We need to get the right conjuct of h18 based on <expert-advice>.
      let h19 := h18.right
      -- False on the left can always be used.
      apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118887845656150200279274585983 : ((True → (p3 ∧ ((((((p4 ∨ True) ∨ ((p1 → p5) → (((False ∧ p3) ∧ (p1 → p5)) ∧ p4))) ∨ p3) ∧ p2) ∨ p5) ∧ p2))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141929946285955861154398186161 : (((p2 ∧ False) → (True ∨ (((p5 ∨ ((p2 ∨ p2) ∧ (p1 ∨ (p4 → (p2 ∧ p4))))) → False) ∧ ((p5 ∧ p3) ∨ p3)))) → ((True → p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302726044160652991455532964177 : (False ∨ (p3 ∨ (p4 ∨ (p4 → (((True ∧ (p3 → (p2 → True))) ∨ (True ∨ (p4 ∨ p5))) → (((((p4 ∨ p1) ∧ p2) → False) ∨ True) ∨ False)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66294866858539115219147465524 : ((p5 ∨ ((p5 ∧ p3) ∨ ((p4 ∧ p2) ∧ (p3 → ((((False → p3) → p4) ∨ (True → (p2 ∧ False))) ∨ ((True ∧ (p1 ∨ p2)) → p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62131474562755411624014751771 : ((p2 ∧ (p4 ∨ (((p1 ∨ (p4 ∨ True)) ∧ (p4 ∧ (p1 ∧ (p5 ∨ ((((p1 → p5) ∧ False) ∧ (p5 ∧ False)) → p5))))) ∧ (p1 → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66083575583918721875706435734 : ((p5 ∨ ((p3 → ((False ∧ ((p3 → (p5 ∧ (p4 → ((p4 ∨ p4) ∧ p1)))) ∨ ((p2 → ((p4 ∧ p1) ∧ False)) ∨ p2))) ∧ p5)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701097315652060321666331339008 : ((((((False ∧ True) ∧ (p3 ∨ ((True ∧ p1) ∨ True))) → False) ∧ (p1 ∨ (((((p3 → p5) ∨ False) ∨ p5) ∨ (p1 → p5)) → (p1 ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135308186934918595408704752499 : (((((((False ∨ p4) ∨ (p5 ∨ p4)) → (True ∨ (p1 ∧ (p2 ∧ p1)))) → (p3 ∨ False)) → p4) ∧ ((p2 → p5) ∧ p1)) ∨ ((p3 ∧ p2) → p3)) := by
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
theorem thm_5_vars_322300941331600565230680705976 : (p5 ∨ ((((p4 ∨ p5) ∧ (p4 ∧ (False ∨ (((((p1 ∨ p1) ∨ p1) → True) ∨ p1) → (p3 ∧ (((p5 → p2) ∨ p4) → False)))))) → p1) ∨ p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : ((((p1 ∨ p1) ∨ p1) → True) ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h10
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h11 := h8 h9
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h13 : ((p5 → p2) ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h14 := h12 h13
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h3.left
    let h17 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h20 : ((((p1 ∨ p1) ∨ p1) → True) ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h21
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h22 := h19 h20
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h24 : ((p5 → p2) ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h25 := h23 h24
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227316399000620665481428436323 : (((p2 → p3) → False) ∨ ((((p1 ∨ ((True ∧ p1) ∧ ((True ∨ True) ∧ (p1 → p5)))) ∨ (p3 → ((False → p4) ∨ False))) ∨ (False ∨ False)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62792964230355291312588605719 : ((p4 ∧ (((False ∨ ((((p4 → p3) ∨ (p5 ∧ (p1 ∧ p2))) → p2) → (p2 ∧ p1))) ∨ p1) ∨ (p4 → (((p5 ∧ True) ∨ p2) → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707049481565925023676282193859 : (((((p4 → ((False ∨ p2) ∧ (True ∧ p4))) ∨ p5) ∨ ((((p5 ∧ True) ∧ p5) ∧ (((p5 ∧ p3) → p4) ∧ p4)) ∨ ((False → p2) ∨ p1))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164572561433060569724542740664 : ((((p4 → (p3 → False)) ∧ ((((True → p4) ∧ (p3 ∧ False)) → (p2 → True)) → p1)) ∧ p4) ∨ (p5 → (((p1 ∨ (True → p5)) → False) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52060187974592618678489438037 : (((p5 → ((p5 ∨ (((p3 ∨ True) ∧ (p4 → p2)) → (False → p5))) → (True ∧ p3))) ∨ ((((p5 ∧ p4) ∨ True) ∨ (p1 ∧ p3)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265782419754253839048547286932 : (True ∧ (p4 ∨ (((True ∨ False) ∧ ((p4 ∨ True) ∨ False)) → (((p5 ∨ p3) ∨ ((True ∧ (p1 ∨ ((p1 → False) → (p5 → False)))) ∨ True)) ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641287257734516135934935575636 : (((((True → p3) ∨ (True ∨ (p4 → (p5 → (((p3 ∨ (((p1 ∧ ((p5 ∧ p3) ∧ (True → p1))) ∨ p2) → p4)) ∧ p3) ∧ p1))))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318890608241494790542064630976 : (p4 ∨ (((p4 ∨ p1) → ((((p3 ∧ (False ∧ ((((p5 ∨ p1) → False) → p2) ∧ p1))) → p2) → p3) ∨ (p1 ∨ p2))) ∨ ((True ∧ True) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46341127137888072627489958214 : ((((p5 ∨ (p5 ∧ (((((True → False) → p4) ∧ p2) → (p5 ∨ p4)) ∨ False))) ∧ ((((p2 → p1) ∧ p2) ∨ p4) ∨ p2)) ∧ (p3 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191675071391617255337521974016 : ((p5 ∧ (((True ∨ p1) ∨ (p3 ∧ p2)) → (p2 → p5))) ∨ ((((False → (p5 ∨ (p4 → True))) ∨ False) → p4) → (True ∧ (p3 → (False ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136335641774818313709636528984 : (((False ∧ ((True → p2) ∨ False)) ∧ (((p1 → False) ∧ (p3 ∨ ((True ∧ (p1 ∧ False)) ∧ (p3 ∨ p1)))) ∧ (p3 → p4))) ∨ ((p5 → p5) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47209738256343203787154484436 : ((((p4 → (p2 ∨ (p4 ∨ (p5 ∨ ((p2 ∧ False) → p1))))) ∧ ((p2 → (p3 ∨ p5)) ∨ (p5 ∨ (p4 ∨ (False ∧ p4))))) ∨ (False → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56275875588706747979125408456 : (((p4 → (p4 ∧ (p1 ∧ False))) ∨ (((p5 ∧ p4) ∨ True) → ((((False → p3) ∧ ((p5 ∧ p3) → True)) → p3) → ((p1 ∨ p3) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750581002447037309089312986880 : (((True ∧ (((((((p1 → (p1 ∧ p3)) → p5) ∨ p3) ∧ ((p5 ∧ (p1 → p2)) ∧ p4)) ∨ p1) → False) → ((p3 ∧ (p1 ∨ p2)) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661700472493411811759600359814 : (((((((((False ∨ (p2 → p3)) ∧ p2) ∨ (p4 → ((p1 → p1) ∧ False))) ∧ p4) → p5) ∧ (p2 ∨ ((True ∧ p1) → p2))) → (True → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118515524336303061562202214559 : ((p3 ∨ ((p5 ∧ (p2 ∧ p2)) ∨ ((((False ∧ p2) ∨ (True ∧ p2)) ∨ p5) ∨ ((True → True) ∨ (((True → p3) ∨ p1) → p2))))) ∨ (False ∨ False)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299093004880950184378744555915 : (False ∨ ((((p1 ∨ (((((p4 → p4) ∧ False) ∧ (((p3 → (p4 ∨ p3)) ∧ True) ∨ p3)) ∧ (p2 ∨ False)) ∧ p1)) ∧ (p3 ∨ p4)) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41495368246842811334039434318 : (((((((False ∨ True) ∧ p5) → ((p4 ∨ p1) ∨ p4)) ∧ (p5 ∧ p2)) → (p2 → (False ∧ ((True ∨ (p1 → p4)) ∨ (p3 ∧ p5))))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668521192477569298242947193986 : (((((((True ∨ (p5 ∧ p2)) ∨ (False → ((p5 ∨ True) → p3))) → (((False ∧ p4) → (p5 → p4)) → p5)) ∧ p2) ∨ ((True → True) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7772382974132994712869008264 : (((((((((((p1 ∨ p2) → p3) ∧ p3) → ((p2 ∨ p4) ∨ p1)) → p3) ∨ False) → p1) ∧ ((False → (p3 ∧ False)) ∧ p2)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314024028071782152378516279410 : (p3 ∨ ((p4 ∨ (p5 → ((((False ∧ p1) ∨ ((((True ∨ p5) ∨ ((p3 ∨ p4) → False)) ∨ p2) ∧ (p2 ∧ True))) ∨ p1) ∨ p1))) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165202507090483812189598566275 : ((((((True ∧ (p2 ∨ (((True ∧ False) → p2) ∨ p1))) ∨ p1) ∧ p3) → p1) ∨ (p5 → p2)) ∨ (((False ∨ p5) ∨ p5) ∨ (True ∨ (p3 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344712220504124121087887221837 : (p2 → (p3 → (((((p3 ∧ (False ∨ p4)) ∧ p1) → ((p3 ∨ (p3 ∨ (p4 ∨ (p2 ∧ p1)))) ∧ False)) ∧ (((p4 ∧ p4) → True) → p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187347208809167508113048301468 : ((p2 ∧ (True ∨ ((True ∨ True) ∧ ((p1 ∧ True) → (p4 ∧ p3))))) → (((p3 ∧ ((False ∨ (p5 → True)) ∨ (p5 ∨ (p4 → False)))) ∧ p5) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41513607582391682987797725625 : (((((p1 ∨ (True ∧ (p2 ∨ ((p1 ∨ True) ∧ p2)))) ∨ False) ∧ ((p3 ∨ ((((True → p4) → p2) ∧ (True ∨ p1)) ∧ p1)) ∧ p3)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609442796476127827756265710673 : (((((True ∧ (((((((p1 ∧ p1) ∨ False) ∧ p4) ∨ p2) ∨ (p5 → (p5 → (p2 → p1)))) ∧ p3) → (p1 ∨ (p1 ∧ p1)))) ∨ p4) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_645513784680400835351296171377 : ((((p4 ∨ (p4 ∧ (((True → (((((p3 ∨ p4) → p1) → (p4 ∧ ((True ∨ p4) → True))) ∧ p3) ∧ True)) ∧ True) ∧ (p3 → p1)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314594121836943761515125669910 : (p3 ∨ (((p3 ∨ p4) → (p4 ∨ ((True → (False ∧ p1)) ∨ ((False ∨ p5) ∨ ((p5 ∧ p4) ∨ p3))))) → ((p3 → p4) ∨ (True ∨ (True ∧ p5))))) := by
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
theorem thm_5_vars_671078541721957774587993783924 : ((((False ∨ ((p2 ∨ p1) → ((p1 ∨ p3) → (p4 → (p4 → ((((p2 ∨ p3) → p5) → p1) → (p3 ∧ True))))))) ∨ (False → (False ∨ p1))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_39597344864754467856884696339 : (((p2 ∨ ((((p3 ∧ True) ∨ (((False → p5) ∧ p4) → ((p4 ∧ p3) ∨ (((False ∨ p4) ∨ p5) → p3)))) → (False → p5)) → False)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148178384180023438541445855640 : (((((p1 → ((p5 ∧ ((False ∨ (p4 → p3)) → p1)) → False)) ∧ p4) ∧ (p4 ∧ p2)) ∧ (False ∨ (p2 ∨ True))) ∨ ((p1 ∨ (p1 ∧ False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343445775283956822086294685189 : (p2 → ((p4 ∨ p3) ∨ (((True → ((False ∨ (((True ∨ True) → (p1 ∨ p2)) ∧ (p3 → False))) ∧ ((True ∧ p3) ∧ p3))) ∨ (p3 ∨ p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111944813407893090904955462168 : ((((True → ((p3 → True) ∨ ((p3 → (p5 ∧ p3)) ∧ p4))) → (p1 ∨ (((False ∨ (True → p1)) ∨ p3) → (False ∧ p5)))) ∨ p2) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350019626494664422781408881895 : (p4 → (((((p4 ∨ p1) → (p4 ∧ (((p5 ∧ ((False ∧ (p1 ∨ p1)) → (p2 → (False → True)))) ∧ p1) ∨ (p5 ∨ p5)))) ∨ p4) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251317808113415276251161527592 : ((p2 → p3) ∨ (((p1 ∧ (False ∨ (p1 ∧ (p5 ∨ p4)))) ∨ (p2 ∧ True)) ∨ ((((p2 ∧ False) ∧ p2) → (p4 ∨ (p1 ∨ p1))) ∨ (True ∧ p4)))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114387884095689227460495654752 : ((((p3 ∨ (p4 ∧ (((True ∧ p1) → True) → ((p4 → p5) ∧ (True ∨ p3))))) ∨ (p1 ∧ p3)) ∨ (p5 ∨ ((p2 → True) ∨ True))) ∨ (p5 → p1)) := by
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
theorem thm_5_vars_48035382872659988081244488891 : ((((p2 ∨ ((p5 ∨ (p1 ∧ (p3 ∧ (p1 ∨ p2)))) ∧ p1)) ∧ ((((p2 ∨ p5) → (p2 ∨ False)) ∨ True) ∨ (p1 ∨ p3))) → (p1 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66605924917856375730833210066 : ((True → ((((((True ∧ p4) ∨ (p4 ∨ (p3 ∨ (False ∨ (p1 → p4))))) ∧ p3) ∨ (p5 ∨ p2)) ∧ p1) ∨ ((p1 ∨ (p3 ∨ True)) ∨ p1))) ∨ p2) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49871808144562114994025091923 : ((((p3 → ((False ∨ False) ∨ ((((p2 ∨ (p5 ∨ ((p2 ∨ p5) ∧ p5))) ∨ False) ∨ p5) ∧ p1))) ∧ p4) ∧ ((True ∧ p1) → (True → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175300476517684961924464772618 : ((p3 ∨ (p5 ∧ (((p4 → (True ∨ True)) ∧ ((p5 ∨ p2) → (False → False))) → p1))) → (True → ((((p4 ∨ p4) ∧ p3) ∨ (True ∨ p4)) ∨ p3))) := by
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
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159039177019898121386655237875 : ((p4 ∨ (p5 → ((((p2 ∧ (p5 → True)) → (p3 ∨ ((True → (p5 → True)) → p1))) ∧ p1) ∨ True))) ∨ ((p2 → p2) ∨ (p5 → (p4 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778355989062584981285677655495 : (((p1 ∨ (p1 ∧ ((False ∨ ((p4 ∨ p2) → False)) ∨ (((p3 ∨ ((False ∧ p4) ∧ p1)) ∧ p3) ∨ (False ∧ (False ∨ ((p3 → p3) ∧ p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186871302764364561717727770625 : (((((p1 ∨ p5) ∨ p4) → True) → (True ∧ ((p4 ∧ p2) ∧ p1))) → ((True ∧ (((p1 → True) → p1) ∨ (False ∨ (p4 ∨ (p4 → True))))) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p1 ∨ p5) ∨ p4) → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305583656864739718007523787182 : (p1 ∨ ((((False ∨ (p1 → p4)) → ((p1 ∧ (p4 ∨ True)) ∧ False)) → p1) ∨ (((((p4 ∧ p4) → p4) → False) ∧ ((p4 ∨ p2) → True)) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 ∧ p4) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53232967614377138334570318284 : (((((p3 ∨ p3) ∧ p5) ∧ ((p1 ∧ True) ∨ ((p5 ∨ p4) ∧ False))) ∨ (p4 → (((True ∨ False) ∧ p5) ∨ (((p3 ∧ True) → p2) → True)))) ∨ p5) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351014340303428838382400124495 : (p4 → ((p1 → (p1 ∧ (p2 → (((p4 → p5) → ((p3 ∨ (False → p5)) ∧ (p3 → p1))) → (False ∧ ((p2 → False) ∧ p2)))))) ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713661827200174652057640727303 : ((((((False ∧ p1) → (p4 ∧ p2)) ∧ p5) → ((p5 ∧ (p4 ∧ (p4 ∧ (((p2 → p4) → (False ∧ (p3 → False))) ∨ (p2 → p4))))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66125399318531019082512471288 : ((p5 ∨ (((p4 ∨ (p5 ∨ ((True ∨ ((p4 → (p2 ∨ p3)) → (p2 ∧ ((True → False) ∧ p3)))) ∨ (p1 → p3)))) ∧ p1) ∧ (p3 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774179089543254250662137023714 : (((False ∨ ((p4 ∨ (True → (((p5 ∧ p2) ∨ (False ∨ (p4 → p4))) ∨ (((((True → p4) → False) ∧ True) → True) ∧ p2)))) → (p4 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172683961054885028108072299467 : (((False ∧ p4) ∨ (p1 ∨ (((True ∨ p4) ∧ ((False ∨ (True → p4)) ∧ p5)) → p3))) ∨ (p5 → (((((p1 ∧ p1) ∨ p1) → p4) ∧ p2) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191276057465541152901142052699 : (((p2 ∨ False) ∧ (True ∨ ((p2 → (p2 ∧ p4)) ∨ p5))) ∨ ((p5 ∧ (p4 ∧ ((p3 ∧ p4) ∧ False))) ∨ (p4 ∨ ((p1 ∨ True) ∨ (True ∨ p5))))) := by
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
theorem thm_5_vars_186327303170760727250650176319 : (((((p1 ∧ p5) ∨ (False ∨ False)) ∧ ((False ∧ p2) ∧ p3)) → p4) → (((p2 ∨ p3) ∨ p3) ∨ (((p4 → (p3 ∨ False)) ∨ (p2 → p3)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115510309439902138878418626837 : (((((p4 ∧ (p4 ∧ True)) ∨ p3) → (p5 ∧ False)) → (p4 ∧ ((((((p3 ∨ p4) ∨ (True ∧ p4)) → True) ∨ p3) ∧ p3) → p3))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307242627923929122852133411702 : (p1 ∨ (p2 ∨ (((((p2 ∨ (p4 ∧ p5)) ∨ (False ∧ p5)) ∨ True) ∨ ((((False ∧ (p5 ∨ (p2 ∨ p3))) ∨ (p3 ∨ p1)) ∨ p3) ∧ p2)) ∨ p3))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148583134382858493667726364750 : (((((p3 ∨ (p1 → p1)) ∧ ((False → p4) → p5)) → p4) ∨ (p4 ∨ (False ∨ (True ∧ (p3 ∨ (True ∨ False)))))) ∨ (p5 ∨ ((p4 → p5) ∧ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248280769008641492351634175418 : ((p2 ∨ p2) ∨ (((True ∨ ((p3 ∨ False) ∧ (p4 → (p2 ∨ p4)))) ∧ True) ∧ (((((p3 ∧ True) → p1) → p5) ∧ p4) ∨ (False → (p3 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315686150169127784129838288997 : (p3 ∨ ((False ∨ p4) ∨ (((p2 → ((p3 ∧ False) ∨ p2)) → p4) → ((True → ((True ∨ ((p2 ∨ p2) ∧ (p1 ∨ p4))) ∧ False)) → (p4 ∧ False))))) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115285929661878608083035290430 : ((((((p1 → p5) ∨ (True → (p2 ∧ p1))) ∧ p5) ∧ p5) → ((((p5 → p5) ∨ False) ∧ (p4 → False)) ∧ (p5 ∨ (p3 ∧ p5)))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329369137769036467132975752654 : (True → ((p1 ∨ (p2 ∧ p3)) → (((p3 ∧ True) → (p4 ∧ True)) → ((p5 → (False ∨ ((p2 ∨ (False ∧ False)) ∨ p1))) ∧ (p2 → (p5 → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Implications on the right can always be decomposed.
  intro h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787115966636740362684836919992 : (((p4 ∨ ((p2 ∧ True) → (True → ((False → ((p4 ∧ p4) ∨ True)) ∧ (p4 → (((p4 → ((False ∨ p3) ∨ p4)) ∨ p4) → (False ∧ p2))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626585020229067315191693798412 : ((((p4 → ((p4 → p2) ∨ (((True → (p5 → (True ∨ ((p3 → p3) → p3)))) → ((p3 ∨ p1) → (p4 → p1))) ∧ (p1 → False)))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_110816281424296875884836069866 : ((((((p4 ∧ False) ∨ (p3 ∨ p4)) ∧ (p3 ∨ (p4 ∧ ((p4 ∧ (p2 ∧ p2)) ∧ (True ∧ ((p2 ∨ p5) ∧ False)))))) ∨ p4) ∧ p4) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357378658583943091652988219371 : (p5 → ((p1 ∧ p5) → (((((p3 ∨ p2) ∨ ((True ∨ p2) ∨ (False ∨ True))) ∨ True) → False) ∨ (True ∧ (((p4 ∨ p1) ∨ p5) → (False ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      exact h3
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307814992039349471616800949508 : (p1 ∨ (p4 → (((p4 → p5) ∨ ((p4 ∧ p3) ∧ p2)) → ((((False ∨ False) ∧ p3) ∧ (p5 ∧ True)) ∨ (True ∨ ((p1 ∨ (True ∧ p2)) ∧ True)))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760670431916991482294091028786 : (((p2 ∧ (p5 ∧ (p3 ∨ ((p5 ∧ (True ∧ p2)) ∨ (False ∧ (((False ∧ p2) ∨ p5) ∧ ((p3 → (p2 ∧ False)) → ((p4 → p2) ∨ p1)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_23673423885838012839414968540 : ((((p3 ∨ (p2 ∨ False)) ∨ p5) ∨ ((p2 ∨ ((((p3 ∧ p5) → ((p1 ∨ True) → p4)) ∧ (False ∨ p3)) ∨ p4)) ∨ ((p4 ∧ p5) → p4))) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319341718531652676799645027025 : (p4 ∨ (((p3 ∨ ((p4 ∧ True) → True)) ∨ ((p5 ∧ p1) → ((p4 ∧ p2) ∧ p4))) ∧ (p1 ∨ (p5 → (p5 → (p3 ∨ ((p4 ∨ p5) ∨ p3))))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



