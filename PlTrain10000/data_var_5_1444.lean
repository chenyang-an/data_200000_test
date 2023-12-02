variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42002174184741692870573568706 : ((((p2 → True) ∧ ((False ∧ p4) ∧ ((((p2 ∧ ((((p2 ∧ False) ∧ False) ∨ (p4 → p3)) → False)) ∧ p2) ∧ (p5 ∨ p2)) → p1))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250920329728851338914292682934 : ((p1 → p3) ∨ (p3 → ((p5 ∨ ((p1 → (p1 ∧ ((p4 ∨ (((p3 ∧ (p2 ∧ True)) ∨ p5) ∧ p1)) → p2))) ∧ (p3 ∧ p4))) ∨ (p5 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337675579347643235294525766441 : (p1 → ((p5 ∧ ((p3 ∨ (False → ((False ∨ p5) ∨ ((True ∧ (p5 → p1)) ∧ (False → True))))) ∧ False)) ∨ ((False ∨ (p2 → (p4 ∨ p1))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245425650519148128967155420514 : ((p2 ∧ p4) ∨ ((((p4 ∧ p1) ∧ (p1 → (True ∨ (p1 ∨ (p1 → p1))))) ∨ p2) ∨ ((p5 → True) ∨ (p2 ∨ ((False ∨ p5) ∨ (False ∨ p3)))))) := by
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
theorem thm_5_vars_749142155053042393126940333710 : ((((p5 → p1) → (((((p4 ∨ False) ∨ ((True ∨ p3) ∨ True)) → ((True ∨ p3) → p2)) ∨ ((p5 → p3) ∧ True)) → ((p2 ∨ p4) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40558745238326251536514679433 : ((((p2 → ((((p2 → (p1 ∧ ((((True ∧ ((p4 ∧ (p4 → p3)) ∧ p2)) ∨ p3) → p2) ∨ False))) ∨ p4) ∧ p1) → p4)) ∨ p2) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309402209173568869352830743380 : (p2 ∨ ((p5 ∨ (p2 ∧ (p3 ∧ (((((((p3 ∧ p1) ∧ p3) → p2) ∧ p2) → p2) ∨ p5) ∧ (p4 ∨ ((p5 → p5) ∧ False)))))) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_96751661272990974203295202296 : ((p1 ∨ (((((p4 → (False ∨ (False ∧ False))) ∧ False) ∨ ((p5 ∧ (p4 → (((p5 → False) ∧ (True → p4)) ∧ p3))) → True)) ∨ p5) → False)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((((p4 → (False ∨ (False ∧ False))) ∧ False) ∨ ((p5 ∧ (p4 → (((p5 → False) ∧ (True → p4)) ∧ p3))) → True)) ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709662683426443576894775070976 : ((((p4 ∨ ((p5 ∧ ((p2 → p3) ∨ False)) → p4)) → (((p4 → ((p5 ∧ ((p2 ∧ ((False ∧ p3) ∨ False)) ∨ True)) → False)) ∧ p5) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304057232524558652703023254018 : (p1 ∨ ((False ∨ ((((p3 → (True ∧ (False ∨ (p4 ∨ ((p2 ∨ (p1 ∧ p4)) ∨ ((p4 ∧ p1) ∧ (p3 → p1))))))) → p1) ∧ p2) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159379776229454444510387266157 : (((((False ∨ True) ∧ ((p2 ∨ p1) ∧ (((p4 → p4) ∨ p4) → ((p3 ∧ p3) ∧ p4)))) ∨ p4) ∧ True) → ((True ∧ (False ∨ p5)) ∨ (p5 → p4))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h6.left
      let h10 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h13 : ((p4 → p4) ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h14
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h15 := h10 h13
        -- We need to get the right conjuct of h15 based on <expert-advice>.
        let h16 := h15.right
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h19 : ((p4 → p4) ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h20
          -- One of the premise coincides with the conclusion.
          exact h20
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h21 := h10 h19
        -- We need to get the right conjuct of h21 based on <expert-advice>.
        let h22 := h21.right
        -- One of the premise coincides with the conclusion.
        exact h22
  case inr h23 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h24
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307353491996219060799045269831 : (p1 ∨ (p3 ∨ (p3 → ((((((p4 ∨ (p5 → p1)) ∨ (p4 ∧ p4)) ∧ p4) → False) ∨ (p2 ∧ p5)) → ((((p4 → p2) ∧ p1) ∧ True) ∨ p3))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56318889172233197623024427075 : ((((p4 ∨ (p2 ∧ p1)) ∧ p1) → ((((p2 → p1) ∨ p3) ∨ ((p4 → ((p5 ∨ True) ∨ p1)) → (False ∨ p4))) → (p1 ∧ (p4 → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699398495638887031733783249793 : (((((True → (((p3 ∧ (p5 → p4)) ∨ p4) ∧ (False ∧ True))) ∧ p4) → (True → (p3 → (((p5 ∧ (p5 ∧ p2)) ∧ (p2 ∧ p3)) ∧ False)))) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h13 := h10 h12
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- False on the left can always be used.
  apply False.elim h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
  have h18 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h16, we can now drive its conclusion.
  let h19 := h16 h18
  -- We need to get the right conjuct of h19 based on <expert-advice>.
  let h20 := h19.right
  -- We need to get the left conjuct of h20 based on <expert-advice>.
  let h21 := h20.left
  -- False on the left can always be used.
  apply False.elim h21
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h22 := h1.left
  let h23 := h1.right
  -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
  have h24 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h22, we can now drive its conclusion.
  let h25 := h22 h24
  -- We need to get the right conjuct of h25 based on <expert-advice>.
  let h26 := h25.right
  -- We need to get the left conjuct of h26 based on <expert-advice>.
  let h27 := h26.left
  -- False on the left can always be used.
  apply False.elim h27
  -- Conjunctions on the left can always be decomposed.
  let h28 := h1.left
  let h29 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h30 := h1.left
  let h31 := h1.right
  -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
  have h32 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h30, we can now drive its conclusion.
  let h33 := h30 h32
  -- We need to get the right conjuct of h33 based on <expert-advice>.
  let h34 := h33.right
  -- We need to get the left conjuct of h34 based on <expert-advice>.
  let h35 := h34.left
  -- False on the left can always be used.
  apply False.elim h35
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322558937283457838079178524425 : (p5 ∨ ((p1 ∨ (p4 ∨ (((((p3 ∨ (p5 ∧ (p1 → ((p3 ∨ True) ∧ (p3 ∨ (p5 → p3)))))) ∧ p1) → (p3 ∨ False)) ∨ p1) ∨ p2))) ∨ p4)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h13 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h14 := h12 h13
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606323105662592465860421453647 : ((((((((p1 ∨ False) ∧ ((p3 ∧ True) ∧ (((p1 ∨ True) ∧ True) → (p4 ∨ ((p3 → True) ∨ (p4 ∧ p5)))))) ∨ p1) ∨ p4) ∧ p5) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644446794938125892204698672522 : ((((False ∨ (True → (p1 ∨ (p4 ∨ (p5 ∨ (((True ∧ (p1 → (p5 ∧ ((p5 ∨ ((p1 → p5) ∨ p4)) → p4)))) → False) ∨ p2)))))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317765393633417948722672323036 : (p4 ∨ ((((((True ∨ ((p3 ∨ p2) → p2)) ∧ p3) → p5) → ((p3 ∨ (p5 ∨ p5)) ∨ False)) → ((p5 ∧ (p1 ∧ p2)) ∨ (p1 → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208237450280928473568785034035 : (((p1 ∧ p1) ∧ (p5 → (p1 ∨ p3))) → ((p1 ∧ ((p5 ∨ p4) ∨ (((p3 ∧ (p1 ∨ ((p1 → p4) ∨ (p2 ∨ True)))) ∧ p4) ∧ p3))) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21499324082333111683110055425 : (((((False ∨ p4) ∨ p5) → (p1 ∨ (False ∨ (p1 ∧ p5)))) ∨ (p4 ∨ (p1 ∨ ((p3 ∨ ((p1 ∧ (p1 → True)) ∧ (p2 ∧ p1))) ∨ True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2221104244866405240560893122 : (((((p2 ∧ True) ∨ p2) ∧ (p2 → (p3 → p1))) ∧ (p1 → ((p1 ∧ p4) ∨ p4))) → (p2 ∧ ((False ∧ p4) ∨ (False ∨ (p5 → True))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h17
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h19
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623382208606544850123082947294 : ((((False ∨ ((True ∧ (((p1 ∧ p2) → ((True ∧ p2) ∨ p1)) → (p4 → (((p5 → ((p3 ∧ True) → p5)) → p3) ∨ True)))) ∧ p2)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_315714318775713281407278066144 : (p3 ∨ ((p5 ∨ p4) ∨ ((p5 ∨ (False ∨ p1)) ∨ ((p1 → False) ∨ (((((p2 → p1) ∧ p2) ∨ False) → ((True ∨ (True ∧ True)) → True)) ∨ p1))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322437665102797439788457904683 : (p5 ∨ (((p3 ∨ ((p4 ∨ (p4 → p2)) ∧ False)) → ((False → (p2 ∧ True)) ∧ ((((False ∨ (p3 ∧ p1)) ∨ (p1 → p3)) ∧ p5) ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339024243204026627556809836007 : (p1 → (True ∧ (((p2 ∧ p1) ∨ (p2 ∧ p5)) → (((p5 ∨ p4) → False) ∨ ((p5 ∨ ((p2 ∧ (False ∧ p1)) → (p1 ∧ (p3 ∧ p2)))) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47538140782287061376425803456 : (((p4 ∨ (p5 → (((p5 ∧ p2) ∨ ((p1 ∨ p2) ∧ p4)) ∧ ((((True → p1) → False) → True) ∧ (p4 ∨ (p1 → True)))))) ∨ (p1 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358654137176391046949462558726 : (p5 → (p4 → ((p3 → (p5 → ((p1 ∨ p1) ∨ (False ∧ ((p1 → (p5 ∧ ((p2 ∧ ((False ∨ True) ∨ p3)) ∧ False))) ∧ p5))))) ∨ (p2 ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326113450621150867346811747148 : (p5 ∨ (p1 → (((p1 → ((((p5 ∨ (True → p2)) ∧ False) ∧ (p4 ∨ True)) → ((p5 → p2) ∧ p3))) → (p1 → p4)) ∨ (True ∧ (True ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_114376527634423621843686844198 : (((((p3 → ((((p2 ∧ (p2 → (False → (p1 → False)))) → p1) ∧ False) ∧ p3)) → p2) → p1) ∨ (((False → False) ∨ p3) ∨ False)) ∨ (p4 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328188130474271374894095558385 : (True → ((((p4 ∨ ((p4 → (True ∨ (True ∧ p1))) ∧ p5)) ∨ False) ∨ ((p5 ∨ (p2 → (p2 ∧ (p3 ∧ False)))) ∧ p5)) → ((False ∧ p4) ∨ True))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256884661836688934264411336018 : ((p1 ∨ p4) → ((p5 ∨ (((p5 ∧ ((p4 ∨ p3) ∨ (p3 ∨ (p4 → ((p5 → False) ∧ p1))))) ∨ p5) ∨ (p1 → (False → (p2 ∨ p5))))) ∨ p2)) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45979236216853139204293277149 : (((((False ∨ ((False ∨ p3) → ((True → ((((p1 ∧ p1) ∨ False) ∨ (p3 ∧ (p1 ∧ p1))) ∨ p1)) ∨ p3))) ∧ p5) ∧ p4) ∧ (p3 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231512617423723879583385077883 : (((p4 → False) ∨ p1) → (False ∨ ((((((p2 ∧ p5) ∧ (p2 ∨ ((p4 ∧ (True ∧ p1)) ∨ True))) ∧ p5) ∧ p3) → (p1 ∧ p4)) ∨ (True ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135365077246408923069604844835 : (((p5 → (((((p2 → (False ∧ True)) ∨ p2) ∨ p2) ∨ ((p3 → p3) → (True → p1))) → p1)) ∧ (p1 → (p2 ∨ p5))) ∨ (False → (p3 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323803335463349922008995891891 : (p5 ∨ ((True ∧ (((p3 ∨ p1) ∨ (((p5 → p4) ∧ (False → p4)) ∨ ((p4 ∧ p5) ∧ p2))) ∧ False)) ∨ ((p3 ∨ p5) → (p4 ∨ (p4 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318654007853652230746321055483 : (p4 ∨ ((p2 → ((p4 ∧ ((p1 ∧ ((True ∨ True) ∨ ((False ∧ False) ∨ p3))) ∧ ((p2 ∧ p4) → p1))) ∨ (True ∧ (p5 → False)))) ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169123237885798351863137538199 : ((p5 → ((p4 ∧ (p2 → (((((True ∧ True) ∨ p3) ∨ p4) ∧ p3) → (p5 → True)))) ∨ p5)) → ((p2 → p5) ∨ (p1 ∨ ((p4 → p4) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655461459311257175681283206783 : (((((False ∨ ((p5 ∨ ((p2 ∨ p2) → (p4 ∨ p5))) → ((p1 ∧ p4) → (p3 ∧ (p3 → (p5 → p5)))))) ∨ (p4 ∨ p1)) ∨ (p4 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674395021143702019717413822755 : ((((p2 ∨ ((((p2 ∨ True) ∧ p2) ∨ ((p2 ∧ ((p2 ∨ p2) ∧ p4)) → False)) → (((p2 → p4) ∧ p2) ∧ p3))) → ((True → False) → p4)) ∨ p4) ∧ True) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587849210136133725987967435746 : ((((((p3 ∨ (p4 → ((p4 ∧ (((p5 ∧ (p1 ∧ p3)) ∧ (((p1 ∧ p1) ∧ p1) ∨ p4)) ∧ p1)) ∨ p2))) ∨ (p4 → p3)) ∨ True) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65066482164979369740571470229 : ((p2 ∨ (p4 ∧ ((((p3 → (p3 ∧ (True ∧ p2))) ∨ p5) ∧ ((p2 ∧ p4) → ((p2 ∧ (p3 ∧ p3)) ∨ (p5 → (False → True))))) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33705275160126086407466940616 : ((p5 ∨ (((((((True ∨ p2) ∧ p3) ∧ p2) ∨ False) → True) → ((((p5 ∨ (p2 → p5)) ∨ False) → p2) ∨ ((p4 → p1) → True))) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58901631409440097458061506814 : (((False ∧ p5) ∨ ((((((p5 ∧ False) ∧ p4) ∧ (True ∨ (((p5 ∧ True) → (p1 ∨ (p2 → p1))) ∧ p4))) ∨ False) ∨ p2) ∨ (p2 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263158277994854290189210738252 : (True ∧ ((p4 ∧ (((False ∨ ((p1 ∧ (p5 ∨ (p1 → (p3 → True)))) ∧ (p4 ∨ (p1 ∨ (p4 ∨ p5))))) ∨ (p2 ∧ p2)) → False)) ∨ (False → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299103484437117184790484775424 : (False ∨ (((((False ∨ p3) ∨ (p5 ∧ False)) ∧ (p2 → (((p3 ∧ (((False ∧ p3) ∨ (p5 ∧ p3)) → False)) ∨ (True → False)) ∨ p2))) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659728564424324553133264984394 : ((((((p2 ∨ p5) → ((((p3 → (p4 ∧ ((False ∧ ((False → p5) ∧ p3)) ∨ p5))) ∨ (p1 ∧ p3)) → p3) ∧ p5)) ∧ p4) → (p2 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148259022542606343887762840653 : (((p4 ∧ (p1 ∨ ((((True → (True ∧ False)) → p2) ∨ (False → (p4 → True))) ∧ p2))) ∨ ((p4 ∨ p1) ∧ p3)) ∨ (p1 ∨ ((p5 ∧ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708552667895983677182061643984 : ((((((p1 ∧ (False → p4)) → (p5 ∨ p2)) ∨ p2) → ((((p4 → p1) ∨ True) ∧ ((p1 → ((False ∧ p3) ∨ (False → True))) ∨ p3)) ∨ p3)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161249243116092717178180291249 : (((p5 ∧ p3) → ((p1 ∨ p1) → ((p1 ∧ False) ∧ (((p3 → p3) → False) → (p2 ∧ (p4 → p1)))))) → (((p1 ∨ (True → p1)) ∧ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1768747901057761211032841851 : (((p1 ∨ ((p4 ∨ p5) ∧ ((((p5 → (False ∨ p3)) ∧ True) ∨ p3) ∧ (p4 ∧ ((p1 ∨ True) ∧ p2))))) ∨ p5) ∨ (p4 → (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245211139137734379228433355320 : ((p2 ∧ False) ∨ (p2 → ((p3 ∨ (False ∧ (True → p1))) ∨ (p2 → ((((p2 ∨ False) ∧ (False ∨ p2)) ∧ True) ∧ (((p3 ∧ p1) ∧ p5) → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64091685708524160652586652444 : ((False ∨ (((p4 → (p4 → (p5 ∧ (p1 → p2)))) ∧ ((p3 ∨ False) → p4)) → (((False → (((p1 ∨ p5) → p3) → p5)) ∧ p2) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219360588317185093406141885114 : ((p3 ∨ ((p5 → p3) ∧ True)) → ((p1 ∧ ((p2 → (p5 → (p2 → p5))) ∨ True)) → (((((p3 → False) ∧ p1) ∨ p4) ∨ p2) ∨ (p5 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728824135744535676577543599753 : (((((p2 ∧ p5) ∧ True) → ((p1 → p3) → (((False → p4) ∧ (True → ((p3 ∨ (True ∨ p4)) ∧ ((p1 ∨ True) ∧ (p2 → p4))))) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208348361198773991765784885534 : (((p5 → False) ∧ (p3 ∧ (p4 → p2))) → ((((p5 ∨ True) ∨ False) → ((p3 ∨ (((p4 → (p1 → False)) ∧ p1) ∧ p2)) ∧ p4)) → (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69341837277482193400773180524 : ((p5 → (p1 ∨ ((((p1 ∨ (p3 ∨ True)) → (p5 ∧ p5)) ∧ ((False ∨ p2) ∧ (((p3 → p1) → p1) ∨ False))) ∧ ((False → p1) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258791465663082677210493682240 : ((True → False) → (((p1 ∧ p2) ∨ (p5 ∧ False)) ∧ ((p4 ∨ ((p1 ∧ p2) → (((p3 ∨ True) → p1) → (p1 → (p1 ∨ (p4 ∧ p4)))))) ∨ p4))) := by
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
theorem thm_5_vars_118820013321448503843313181150 : ((True → ((((((p2 → p3) ∧ ((p4 → (p2 ∧ True)) ∨ (True ∨ (False ∧ True)))) → p3) → (p2 → (p1 ∨ p3))) ∨ p2) → p3)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354265142675319493667018454582 : (p5 → (((((p4 ∧ (((p2 ∧ (p5 ∨ (p3 → p2))) → p1) → (((True ∧ p4) ∨ p3) → p3))) ∨ p4) ∨ (p5 ∨ p3)) ∨ (p2 → True)) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198231145309140451706081744776 : ((True ∧ ((p1 ∨ (p1 ∧ True)) ∨ (p5 ∧ True))) ∨ ((p2 → (((((True ∧ (p1 → False)) → p5) → p3) → p5) ∨ p3)) ∨ (False ∨ (False → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703625301071523444620445588730 : ((((p5 → ((((True ∧ p4) → p3) ∧ True) ∧ (True → False))) ∨ ((p1 → (p3 ∧ ((p3 ∨ ((p1 ∧ (p5 ∧ p2)) ∨ p4)) ∨ p4))) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_753249021403752940752441532623 : (((False ∧ (((True ∧ (p1 ∧ p1)) ∧ (p3 ∨ (((False ∨ p5) ∧ ((p5 → False) → False)) ∨ (((p3 ∨ p4) ∧ p2) ∨ p5)))) ∨ (False ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756180165769597977548454146336 : (((p1 ∧ (((((p5 ∧ (((p5 ∨ p5) ∧ False) ∨ ((p5 ∨ p2) ∨ (True → (False ∧ (True ∧ True)))))) ∨ p1) → p2) ∧ p2) ∨ (True → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171302874640775620208997036168 : (((((p4 ∧ (p5 ∨ (False ∨ p2))) ∨ (((p1 ∧ p3) ∧ p5) ∧ p3)) ∧ False) ∧ p5) ∨ ((p5 → (p5 ∧ p2)) → (p4 ∨ ((False → p5) ∨ p4)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696598029973054646576313676117 : ((((((p1 → ((p5 ∧ (p1 ∨ p1)) → False)) ∧ (p1 ∨ p5)) ∨ p3) ∧ (p2 ∨ ((p1 → (((p5 → False) ∧ p1) ∨ p4)) → (p3 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758499018191953953437165015135 : (((p2 ∧ ((p5 ∨ ((False ∨ (p1 ∨ p2)) ∧ (((((False → True) → ((p1 → p3) → (p3 ∨ p3))) ∧ (p4 ∨ p5)) → p3) ∧ p5))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180994367430227835438845723943 : (((p3 ∧ p5) ∨ ((p1 ∧ (((p2 ∧ p3) ∨ (p4 ∧ p2)) ∨ p3)) ∧ p3)) → (p2 → (False ∨ (False ∨ (p2 ∨ (((False ∨ p2) ∧ False) ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342607619766687848384683981381 : (p2 → (((True → False) ∧ (p1 → ((p5 ∨ p1) ∧ ((p3 ∨ p2) → p1)))) → (((((p3 ∨ False) ∧ p2) ∧ ((p1 ∨ p4) ∨ p4)) ∧ p4) ∧ p5))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h12 := h9 h11
  -- False on the left can always be used.
  apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h2.left
  let h14 := h2.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h15 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h16 := h13 h15
  -- False on the left can always be used.
  apply False.elim h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h2.left
  let h18 := h2.right
  -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
  have h19 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h17, we can now drive its conclusion.
  let h20 := h17 h19
  -- False on the left can always be used.
  apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117544036305117757276152928031 : ((p2 ∧ (((p5 ∨ ((((p5 → (True → p2)) ∨ False) → True) → ((p4 ∨ (True → p2)) ∧ p1))) → p5) → (p1 ∨ (True → p2)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136578411117136966968795802095 : (((False ∧ (p3 ∧ True)) ∨ ((((p1 ∧ p2) ∧ True) ∨ (p1 → p4)) → ((False ∨ p5) → (((False → p4) ∨ p1) → False)))) ∨ ((p2 ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339847248936243784573607793760 : (p1 → (True → ((((True ∨ (p5 ∨ p4)) ∨ p2) → (((((p3 ∧ p2) ∧ p2) ∨ True) ∨ ((p5 ∨ True) → p3)) ∧ (p4 ∨ (p5 ∨ True)))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238724286973970843261855888742 : ((p1 ∨ True) ∧ (((((False ∧ p1) → p4) ∧ (p4 ∧ (p3 ∧ (p3 → True)))) → (p5 ∨ (((p5 ∨ p5) ∨ (p3 ∧ False)) ∨ (p4 ∨ p4)))) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228773747692556636070458661536 : ((p3 ∨ (p3 ∧ p1)) ∨ ((((p5 → ((p1 → True) ∨ (p5 ∧ p1))) → p2) ∨ ((((p2 ∨ p5) ∧ p2) ∨ (False → p5)) ∧ p3)) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84498939762085626102262673970 : (((((p4 ∨ (((p3 ∧ p5) ∧ (True → p4)) ∨ (p5 ∧ p1))) → True) ∨ (p2 → p4)) → (p5 ∧ (p3 ∧ ((p3 → (p4 ∧ p1)) ∧ False)))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∨ (((p3 ∧ p5) ∧ (True → p4)) ∨ (p5 ∧ p1))) → True) ∨ (p2 → p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184916001308491730279923045122 : ((((True → p3) → p4) ∨ ((p1 ∨ ((p1 ∨ False) ∨ False)) ∧ p3)) ∨ ((p1 ∨ (p1 → ((p3 → ((p4 ∧ p4) ∨ p2)) ∨ (p5 → p1)))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136824555596052047267349156098 : (((True ∧ p4) ∨ (p4 → (((p3 ∨ ((p2 ∨ False) ∨ p4)) ∧ p3) → (((p1 ∧ True) ∧ p4) ∨ ((p1 ∧ p5) ∧ p5))))) ∨ (p5 → (p4 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351738405977136297244885762264 : (p4 → ((True ∧ ((p2 ∧ (p5 ∨ p3)) ∨ (((p5 ∨ True) → (p5 ∨ p1)) ∨ p4))) ∨ (p2 ∨ ((p4 ∧ p4) ∧ (p2 → (False → (p5 ∧ p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_720042348602518738621617190111 : ((((((False → False) ∨ False) ∧ p1) → (p5 → (((((True ∧ (p4 ∧ (p3 → p5))) ∨ p5) → (p4 → p2)) ∨ ((p5 → p3) → False)) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62848685071267729546566930528 : ((p4 ∧ ((((p2 ∨ p2) ∧ p3) → p1) ∧ ((p4 → p3) ∨ ((p1 ∧ (((True ∧ ((p1 ∧ p4) ∧ p3)) ∧ False) ∨ (True → p5))) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219069357146450672896106160076 : ((p5 ∧ (p2 ∨ (p3 → p3))) → (p2 ∨ (((p1 ∨ ((True → False) ∧ p3)) ∧ (False ∨ ((((p4 → p1) ∨ p4) ∧ p2) ∧ (p2 ∨ p5)))) → p1))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h12.left
        let h15 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h17 =>
            -- One of the premise coincides with the conclusion.
            exact h9
          case inr h18 =>
            -- One of the premise coincides with the conclusion.
            exact h9
        case inr h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h20 =>
            -- One of the premise coincides with the conclusion.
            exact h9
          case inr h21 =>
            -- One of the premise coincides with the conclusion.
            exact h9
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h25 =>
        -- False on the left can always be used.
        apply False.elim h25
      case inr h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- Conjunctions on the left can always be decomposed.
        let h29 := h27.left
        let h30 := h27.right
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h31 =>
          -- Disjunctions on the left can always be decomposed.
          cases h28
          case inl h32 =>
            -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
            have h33 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h23, we can now drive its conclusion.
            let h34 := h23 h33
            -- False on the left can always be used.
            apply False.elim h34
          case inr h35 =>
            -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
            have h36 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h23, we can now drive its conclusion.
            let h37 := h23 h36
            -- False on the left can always be used.
            apply False.elim h37
        case inr h38 =>
          -- Disjunctions on the left can always be decomposed.
          cases h28
          case inl h39 =>
            -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
            have h40 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h23, we can now drive its conclusion.
            let h41 := h23 h40
            -- False on the left can always be used.
            apply False.elim h41
          case inr h42 =>
            -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
            have h43 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h23, we can now drive its conclusion.
            let h44 := h23 h43
            -- False on the left can always be used.
            apply False.elim h44



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113520471660295740899118665450 : ((((p3 ∨ (p2 ∨ ((p5 ∨ (p2 → (p2 ∧ p4))) → False))) ∨ (((p1 → p3) → True) ∧ (p1 → (p1 ∨ p2)))) ∨ (p5 ∨ p2)) ∨ (p5 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55843786245208279553947867288 : (((p1 ∧ (p2 ∨ (p3 → p2))) ∧ (((p1 ∧ False) ∧ True) ∧ (((p3 → ((p3 ∧ (False ∨ (False ∧ (p5 → p3)))) ∧ p1)) ∧ p1) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199619988537709865781567094746 : (((((False → p3) ∨ p2) ∧ (p1 → True)) → p2) → ((p1 ∨ (False ∧ ((False ∨ (p5 ∧ (p2 ∧ p4))) ∧ (p5 → ((p4 ∨ p3) → p3))))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False → p3) ∨ p2) ∧ (p1 → True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56450814604693326479327305367 : ((((p5 ∨ False) ∨ (p4 ∨ True)) → (p4 ∧ (p2 ∨ (True → (p3 → (p4 ∧ (((p3 → True) ∧ ((p5 → (True → p1)) ∨ False)) ∧ p4))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694372841448155130459746419088 : (((((p1 ∨ p2) ∧ (((((p2 → False) → (p3 ∨ p2)) ∧ False) ∨ p5) ∨ p1)) ∨ ((True ∨ (p2 ∨ (p5 → ((p1 → p3) → p1)))) ∨ p5)) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752636614846726453446229226033 : (((False ∧ ((((p2 ∨ (p4 → ((p3 ∨ (p3 → (((p1 ∨ p5) ∨ False) ∨ p4))) ∧ (p1 ∧ False)))) → ((p5 → p4) ∧ p5)) → p2) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246460876199700939037379920297 : ((p5 ∧ False) ∨ (((p1 ∨ False) → (p4 ∨ ((p5 ∨ p3) → p5))) ∨ (p2 → (((p4 ∨ p5) ∨ ((False → (p3 ∧ p3)) ∧ (True ∨ p4))) ∨ p5)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613634877944699352022053177342 : (((((((p4 ∧ (False → (((p4 → ((p2 → False) → False)) ∧ p4) → p2))) ∨ p5) ∧ (p4 ∨ (True ∨ p2))) ∧ (p1 ∧ (p3 ∧ False))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51589704747976354896380509975 : (((p1 → (((False ∧ (False ∨ ((p2 ∧ (((p4 → p4) ∨ p1) ∧ p3)) ∧ True))) ∧ p4) ∧ p4)) → (p2 → (p4 ∧ ((p3 → True) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40118309753527836284150387236 : ((((((p1 → p3) ∨ ((((False ∧ (p3 → (True ∧ p2))) ∨ False) → (p3 ∨ (p3 → (p4 → p1)))) → p2)) → (False ∨ p3)) ∧ p5) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184549968094182611982487914412 : ((((((False → p1) → p2) → (p5 ∧ p1)) → p2) → (p2 → False)) ∨ (((p1 ∧ (p2 ∧ (((p3 ∨ p2) ∧ p2) ∨ p1))) ∨ (p2 → True)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310625878127292451586254021731 : (p2 ∨ (((p1 ∧ False) ∨ (p5 ∨ p5)) ∨ ((((False ∧ p5) → True) ∨ (((p4 ∧ True) ∨ ((False ∧ (False ∨ (p5 → p2))) ∧ p5)) ∨ p2)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_98963044331648721328021882946 : ((True → (((p4 ∨ (((p5 ∧ ((False ∨ True) ∨ p4)) ∧ p3) ∨ (((p5 ∨ p3) ∧ True) → p2))) ∧ False) ∧ ((p4 ∨ (p1 → p1)) ∧ p1))) → p1) := by
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136674915004502448511933910615 : (((p5 ∨ (False ∨ p3)) → (p2 → ((p3 ∧ ((p4 ∨ (((False ∧ p3) ∨ p2) ∧ p4)) → False)) ∧ ((p4 ∧ p1) → True)))) ∨ (p5 → (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160504541868878666113222922288 : ((((p3 ∧ p5) ∧ (((p3 ∧ p5) ∧ p3) → ((p2 ∨ False) ∧ True))) ∧ (((True ∨ True) ∨ p4) ∨ True)) → (p1 ∨ (p4 ∨ (p2 → (p2 ∧ p3))))) := by
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
  cases h3
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h11
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h13
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h16
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137988017305033296586370526342 : ((p5 ∨ (True ∧ ((((p2 → p1) → (p5 ∨ (p5 ∧ True))) → ((((False ∨ p5) → (p1 ∨ p1)) → p4) ∨ p3)) ∧ p1))) ∨ ((p2 ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350050202717448094563311769775 : (p4 → (((p1 → (((p4 ∧ (p5 ∧ ((p5 → (p4 ∧ ((p3 ∨ p3) → (p2 → p1)))) → (p5 ∨ (p5 ∧ p4))))) ∨ p5) → p5)) → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49300567170356934578467339536 : (((False ∨ ((((p3 → (((p1 ∧ p1) ∧ p3) ∧ p2)) → p5) → (p1 ∨ p5)) → ((p2 ∧ (p5 → True)) → False))) ∨ ((False ∧ p2) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102681095817765664697432328209 : ((((((((p3 ∨ p4) → ((((False ∧ (p4 → p4)) ∨ p2) → (p5 → (p2 → False))) → p5)) ∨ p2) → p3) ∨ p5) ∨ True) ∨ p3) ∧ (p3 → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171603614197278920091658604626 : ((((p1 → ((False ∨ (p5 ∨ p2)) ∧ True)) ∨ ((p4 → (False → p3)) → p2)) ∨ False) ∨ (True ∨ ((((p4 ∧ p4) → True) ∧ (True ∨ p1)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



