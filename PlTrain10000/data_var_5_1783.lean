variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355867362983884691943472618235 : (p5 → ((((False ∨ p5) ∧ p2) ∧ ((((p2 → p3) ∧ p2) → ((p3 ∧ p4) ∨ p4)) ∨ ((p1 → p3) ∨ (p4 → p3)))) ∨ ((False ∨ True) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158436687018224503546837498284 : (((p1 ∨ p2) ∨ (p5 ∧ (p2 → ((((p2 ∨ ((p4 ∧ p3) → p3)) ∨ (p4 ∧ False)) ∧ p3) → p1)))) ∨ (True → ((True ∧ (p5 ∨ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179782566300025474788475620254 : (((((p2 ∨ p4) → False) ∧ (((p5 → p3) → (p1 → p2)) ∨ p1)) ∧ p2) → ((((p1 ∨ (p2 ∨ p5)) → (True ∧ (p3 ∧ True))) → p3) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : (p2 ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h11 : (p2 ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h12 := h5 h11
    -- False on the left can always be used.
    apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h13.left
  let h16 := h13.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h17 =>
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h18 : (p2 ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h19 := h15 h18
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46100324711221690001569622478 : (((((False ∨ p4) ∧ (False ∨ (p5 ∧ (p2 ∧ (((True ∧ p4) → ((p2 → p3) ∧ (False ∧ (p1 ∨ p1)))) ∨ p3))))) ∨ True) ∧ (False → False)) ∨ p3) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780919364551247106093370550221 : (((p2 ∨ (((False ∧ p5) ∨ False) ∨ (((((p3 → False) ∧ ((((p5 → (p4 ∧ p4)) → p3) ∨ p2) ∨ (True ∧ p5))) → p4) ∧ p5) ∨ True))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64380849955063193476589013883 : ((p1 ∨ ((p5 ∨ ((p4 ∧ p1) → ((((((True ∧ (p1 ∨ p4)) ∨ False) → p5) ∨ p2) ∧ p5) ∨ ((True → (p5 ∨ p4)) ∨ p1)))) ∨ p1)) ∨ p1) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47640752599942647150625322878 : (((((p4 → ((((p3 ∧ (p5 ∧ ((False → p5) ∧ True))) → p1) → ((p3 ∨ p5) ∨ p3)) ∨ (p1 → p3))) ∨ p2) ∧ p2) → (p1 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118877944261207611165260793522 : ((True → ((p2 → p4) ∨ ((p3 ∧ (p3 ∧ False)) ∨ (((p4 ∧ (p5 ∧ p1)) ∧ p4) ∨ (False ∨ ((p2 ∧ p4) ∧ (True ∧ p5))))))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260536231989613472801541479625 : ((p3 → p1) → (((((p3 ∧ p2) ∨ (p1 ∧ ((p1 ∨ p1) → (p3 ∧ ((False ∧ p4) ∨ ((p3 ∧ p4) ∧ p5)))))) ∨ False) ∧ p1) ∨ (p3 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205465178202295995954024679117 : (((p2 → (p1 → p4)) → (p5 ∧ p5)) ∨ ((False ∧ ((((p2 ∨ True) ∧ (False → False)) → ((p1 ∨ ((p5 ∧ p1) ∨ p1)) → p4)) ∧ p5)) → p2)) := by
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
theorem thm_5_vars_459082977795414108340206319184 : ((((((p3 ∨ ((((p2 ∧ (True → p5)) ∧ (p3 → False)) ∨ (False ∧ p4)) → p2)) → p1) ∨ True) → (((False ∧ p3) ∧ (p3 ∨ p1)) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61943379516817628266671349535 : ((p2 ∧ ((((((p5 → (((p2 → p3) → p4) → p3)) ∨ p4) ∨ p2) ∧ p2) → (p3 → p4)) ∨ ((((False ∨ p4) ∧ p4) ∧ p1) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322498634614999493038220350420 : (p5 ∨ (((p3 ∨ p5) → (p5 ∧ ((False ∨ ((((((p1 ∧ p1) ∧ p4) ∧ p4) ∧ ((True ∨ p3) ∨ (True → True))) ∨ True) → False)) → p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305229085104467936607380037292 : (p1 ∨ (((True → (p1 ∧ p3)) ∨ (((p3 → (((p2 ∧ p2) → p5) ∧ p5)) ∧ p5) ∧ ((p2 → p4) → p1))) → ((p1 ∧ True) ∨ (p1 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We need to get the left conjuct of h4 based on <expert-advice>.
    let h5 := h4.left
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116175452809557764026097065313 : (((p2 → (p2 ∧ p5)) ∧ ((p5 ∨ ((False ∧ ((p5 ∨ p1) → (((p1 ∨ (p2 ∧ p4)) ∧ True) ∧ False))) ∧ (p3 ∧ p3))) ∨ True)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244824595700849398139016527886 : ((p1 ∧ p1) ∨ ((p4 → (p5 → (True → p1))) ∨ ((p3 ∨ (False ∨ (False → ((((p1 ∧ True) ∧ p3) ∨ (True ∨ False)) ∧ (p5 → p1))))) ∨ False))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112171392655489389891358720804 : (((p3 ∧ (p4 ∨ ((p2 ∧ ((p4 ∨ (p4 ∧ p3)) → (p1 ∨ (((True → p4) → (p1 → p1)) → (p1 ∨ p2))))) ∨ p3))) ∨ True) ∨ (p5 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51460401493110207283252307634 : ((((p3 ∨ (True ∨ ((p4 → (True → (p3 → p4))) ∧ p2))) ∧ (((p2 ∧ p2) ∨ p4) ∧ p4)) → (p4 → ((p4 → (p4 → False)) → False))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h12
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h14 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h15 := h13 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h17 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h18 := h3 h17
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h19 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h20 := h18 h19
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h5.left
      let h24 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h28 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h24
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h29 := h3 h28
        -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
        have h30 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h24
        -- We have shown the premise of h29, we can now drive its conclusion.
        let h31 := h29 h30
        -- False on the left can always be used.
        apply False.elim h31
      case inr h32 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h33 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h24
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h34 := h3 h33
        -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
        have h35 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h24
        -- We have shown the premise of h34, we can now drive its conclusion.
        let h36 := h34 h35
        -- False on the left can always be used.
        apply False.elim h36
    case inr h37 =>
      -- Conjunctions on the left can always be decomposed.
      let h38 := h37.left
      let h39 := h37.right
      -- Conjunctions on the left can always be decomposed.
      let h40 := h5.left
      let h41 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h40
      case inl h42 =>
        -- Conjunctions on the left can always be decomposed.
        let h43 := h42.left
        let h44 := h42.right
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h45 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h41
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h46 := h3 h45
        -- We want to use the implication h46 based on <expert-advice>. So we show its premise.
        have h47 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h41
        -- We have shown the premise of h46, we can now drive its conclusion.
        let h48 := h46 h47
        -- False on the left can always be used.
        apply False.elim h48
      case inr h49 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h50 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h41
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h51 := h3 h50
        -- We want to use the implication h51 based on <expert-advice>. So we show its premise.
        have h52 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h41
        -- We have shown the premise of h51, we can now drive its conclusion.
        let h53 := h51 h52
        -- False on the left can always be used.
        apply False.elim h53



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38438376965164469722324577882 : (((((True ∨ (p5 ∨ (p2 → p3))) → (p2 ∨ (p2 ∨ ((True ∨ p2) ∨ p2)))) ∨ (((p3 ∨ p2) → p1) ∧ (p5 ∨ (p5 → False)))) ∧ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
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
    case inr h5 =>
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204252593132452831051168366059 : ((((p4 → p2) ∧ (p5 ∧ False)) ∧ True) ∨ ((p1 ∨ ((((((p1 ∧ p1) ∨ (p2 ∨ (p1 → p4))) → (p3 → p1)) ∨ p3) → False) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225991990990180178144527710579 : (((p3 ∧ p5) ∨ p3) ∨ (((p4 → (False ∨ (((True ∧ p2) ∨ False) ∨ (p3 ∨ p1)))) ∨ (p3 ∨ (p4 ∧ p2))) ∨ (((False ∧ p3) ∧ p1) → False))) := by
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
theorem thm_5_vars_603044669362480638002595866267 : ((((p1 ∨ (p2 ∨ (((p5 → (((p2 ∧ (False → ((p3 → (False → p2)) → p1))) ∧ (p2 → (p3 ∧ p1))) → p1)) ∧ p4) → False))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654711885043484104276644377257 : ((((((((((True → p5) → p2) ∧ (((p4 ∧ False) ∧ (p4 ∨ p4)) ∧ p1)) → p2) ∧ ((p5 ∧ p1) → p1)) ∨ True) → p3) ∨ (True ∨ p2)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317930950275886444839552940590 : (p4 ∨ ((p1 ∨ ((((p3 ∧ (p1 → ((False ∨ ((p2 → p4) ∨ True)) → (p5 ∧ (False ∧ (p2 → False)))))) ∨ (p3 → p4)) ∧ True) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158041791309573418998487166284 : ((((p4 → ((p4 ∧ False) ∧ p3)) ∨ False) ∨ ((True ∨ False) → (p1 ∨ (((p4 ∨ p2) ∨ p4) ∨ p1)))) ∨ (((p4 ∨ (True ∨ p3)) ∨ p5) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167908424504187394338547943042 : ((((p3 → p4) → (p1 → ((True ∨ p5) ∧ p3))) ∧ ((p2 → False) ∧ (p1 ∨ (p5 ∧ False)))) → ((p3 ∧ ((p5 ∧ p4) ∧ True)) ∨ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307517302094289792160148732014 : (p1 ∨ (True → ((False → p3) ∧ (((False ∧ (True ∧ (p5 ∨ ((p1 ∨ (p5 ∧ p3)) ∨ (p1 → True))))) ∨ True) ∧ (p3 → (p2 ∨ (False → p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171314599855218041780224497929 : ((((((p4 → False) ∧ ((p4 → (p4 ∧ p2)) ∨ (p3 → False))) ∧ p2) ∨ p1) ∧ p4) ∨ (p1 ∨ ((p1 → (True → p1)) → ((p2 ∨ True) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313257137931636073619790277711 : (p3 ∨ (((p5 → p4) → (((p1 → (p5 ∨ ((False ∧ p1) ∧ ((p2 ∧ p1) ∧ (((True ∧ True) → False) → p2))))) ∨ (p2 → False)) ∨ True)) ∨ p2)) := by
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
theorem thm_5_vars_200858473301188168141231137970 : ((True ∨ (p4 ∧ ((p2 → (p5 ∧ p1)) ∨ p1))) → (((((p3 ∧ (p4 ∨ p1)) ∨ p4) ∧ ((p4 ∨ p3) ∧ p1)) ∨ (p1 ∨ (True ∨ p4))) ∨ p2)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
    case inr h7 =>
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
theorem thm_5_vars_739587763500520862960236707790 : ((((p5 ∧ p3) ∨ ((p2 → p2) ∧ (False ∨ (p3 → (((p5 ∨ p2) → (((True ∧ p1) ∨ ((p1 ∨ p5) ∨ p2)) ∧ p5)) ∧ (p4 ∨ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744314794605134622606031348130 : ((((p1 ∧ p4) → (p1 ∧ ((p2 ∧ (True → p2)) ∧ ((((((True ∨ p2) ∨ p3) ∧ True) ∨ p3) → (p1 ∧ ((True ∧ p3) ∧ p3))) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139414412278140114632918914281 : ((((((p4 → p5) ∨ ((((p2 ∨ (p5 ∧ True)) ∨ p2) → p3) ∨ p4)) ∨ ((p2 ∧ p4) ∨ (False → p2))) ∧ True) → True) → (p3 → (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339785582065539081686843009012 : (p1 → (p5 ∨ (((((((p4 ∧ p4) ∧ p4) ∧ False) → p2) ∧ (p3 ∧ ((p5 ∧ False) ∨ (False ∧ p1)))) ∨ (p4 ∨ ((p5 ∧ True) ∧ p4))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197238144907942063338388322203 : (((((True → (False ∨ p4)) ∨ True) → p3) → False) ∨ ((p2 → p1) ∨ (p2 ∨ (False → (p5 → ((p2 → (True ∧ (p3 → (p4 ∨ True)))) → p2)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166231555349005054109332168062 : ((p2 ∧ ((p2 ∨ p2) ∧ ((((p1 ∧ ((p5 → (p3 ∨ True)) ∨ p1)) ∧ False) ∨ False) ∧ p5))) ∨ (((True ∧ True) → p4) ∨ (False → (p5 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197432478028244626319876553347 : (((((p4 ∧ p4) ∨ p1) ∧ False) ∧ (p1 ∨ True)) ∨ ((p4 ∨ (p4 ∨ (True ∧ ((p1 ∧ p2) → True)))) → (True → (((p5 → False) ∧ False) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116352638296578518780992379325 : ((((p4 ∨ False) ∨ p2) → ((((((False ∨ p1) → p4) ∨ p3) ∧ p3) → False) ∨ (((p3 → p3) ∨ p4) ∨ (p1 → (True ∧ False))))) ∨ (p3 ∨ p5)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685613272160090536969319643352 : ((((((False → ((p3 → ((True → ((True ∨ False) ∧ p4)) ∨ (p2 ∨ p3))) ∨ p4)) → p5) ∨ p1) → (p4 ∨ (p2 → ((False ∨ p3) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247876608027780376243518618199 : ((p1 ∨ p2) ∨ (p1 ∨ (((((p5 ∨ p5) ∧ p5) ∨ (True ∧ p2)) ∨ (True ∨ (p3 ∧ ((((p1 ∨ p5) ∨ p1) ∨ p1) → p4)))) ∨ (p3 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64489651527814809550027083485 : ((p1 ∨ ((((p5 → ((p1 → (p1 ∨ p1)) ∧ (True → p5))) ∨ (False ∨ (p5 ∨ p1))) ∨ True) ∧ ((p2 ∧ (p3 ∨ (p1 ∨ True))) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62384303164264679484925269434 : ((p3 ∧ ((((False ∧ (p5 ∨ ((p1 ∧ (p4 → True)) ∨ p4))) ∧ True) ∨ p3) ∧ (False ∨ (((p4 ∨ p5) → p3) → (p1 → (False ∨ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42181164662490861785341164959 : (((True ∧ ((True ∨ (((p4 ∨ p2) ∨ (False → (((((p5 ∨ p3) ∨ p1) ∨ False) ∨ (p5 ∧ (p1 ∧ p1))) ∨ True))) ∧ p2)) → p1)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_91019559713455893024970742331 : (((p1 → p4) ∧ ((((p2 ∨ p4) ∧ ((p3 ∨ ((p3 → ((p2 → (p3 → True)) → p2)) → (p4 ∧ p3))) → (p5 ∧ p3))) → p5) ∧ p1)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226860969933254971684259008035 : (((p5 ∧ True) → False) ∨ ((p5 ∨ (p3 ∧ (((((p3 ∨ p4) ∨ p2) ∨ p5) → ((p3 ∧ (p3 ∨ ((p3 → p2) → p2))) ∧ False)) ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164886457486404130837705488901 : (((p3 → ((True ∧ (((p2 ∨ (p1 → False)) ∨ (p4 ∧ p1)) ∨ p3)) ∧ (p5 ∨ p5))) ∨ p1) ∨ (p1 → ((p4 ∧ (True ∧ p1)) ∨ (p1 → p1)))) := by
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
theorem thm_5_vars_675875740738813771621825514707 : ((((((True ∧ (p2 ∨ (p5 ∨ (p3 ∨ (p3 ∧ p5))))) ∨ (p2 ∧ p1)) → ((p3 ∧ p5) ∧ (p1 ∨ p4))) ∧ ((p4 ∨ False) → (False ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66267322681225182316703132383 : ((p5 ∨ ((p2 → (p2 ∧ p4)) ∧ ((p4 ∧ (((p2 → p5) ∧ (p5 → ((p4 ∧ p5) ∨ (p3 → True)))) ∧ ((p5 ∧ p3) ∨ p1))) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168653068463872120340581851874 : ((p4 ∧ ((p1 ∨ p2) → (True ∧ ((((p5 → (p3 → p4)) ∧ p2) → (False → p2)) ∨ True)))) → ((((True → p5) ∨ (p5 ∨ False)) → False) ∨ True)) := by
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
theorem thm_5_vars_113796732360928695284597451518 : ((((False → p2) ∨ (True → (False ∧ ((p5 ∧ p5) ∨ ((False ∨ (p3 → (True → (p5 → p2)))) ∨ (True ∨ True)))))) → (p3 ∧ p5)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216801590526165624113456345550 : (((p1 ∧ (p1 → p3)) ∧ p3) → (False ∨ (((p5 ∨ p1) ∨ p1) ∧ (p2 ∨ ((p5 ∧ (p4 → p5)) ∨ ((p2 ∧ (False → (False → p2))) ∨ p1)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227816638454593543482010925258 : ((p2 ∧ (p1 ∧ True)) ∨ (p1 ∨ (p4 ∨ ((((True → (True → p1)) → p3) ∨ (p5 ∧ p1)) ∨ (True ∨ (((p1 ∧ True) ∧ (p3 ∨ p4)) ∨ True)))))) := by
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
theorem thm_5_vars_258626044944918721653643602959 : ((p5 ∨ p4) → (p1 ∨ ((p3 ∧ True) ∨ (((((False ∧ ((p5 → p3) → (p5 ∨ p2))) ∨ (p4 ∨ p5)) ∧ (p1 → True)) → p3) → (p4 ∨ p3))))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (((False ∧ ((p5 → p3) → (p5 ∨ p2))) ∨ (p4 ∨ p5)) ∧ (p1 → True)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185534205974326451151623693218 : ((p3 ∨ ((p4 ∧ p3) ∨ (((p1 ∨ p5) → p1) ∨ (p3 ∨ True)))) ∨ (p1 ∧ (((((p3 ∨ ((True ∨ p3) → True)) → p5) → p5) ∨ p5) ∨ False))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310834116212509357958900409124 : (p2 ∨ (((False ∨ p5) ∧ p1) → (((((p2 ∨ p5) ∧ p4) ∨ p4) ∨ p3) ∨ (((False → p5) ∧ p1) → (((True ∨ (p3 ∨ p4)) ∨ p4) ∧ p5))))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h9 := h6.left
    let h10 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136348943136524747159828752372 : (((True → ((p1 ∧ p5) ∨ p2)) ∧ (((True ∧ (False ∨ ((True ∧ p2) → p4))) → True) → (p3 → (p3 → (p2 → p4))))) ∨ ((True ∨ False) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138475108802337766150954753848 : (((((((p5 ∧ p3) → ((True ∧ p3) ∧ ((p2 ∧ (True → (p2 ∧ p1))) → p3))) ∨ (False ∧ p4)) ∨ p5) ∧ True) ∧ True) → ((p2 ∧ p1) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69830119791121424379603684847 : (((((p3 ∨ ((True → ((p5 ∧ p5) ∨ p1)) ∨ p3)) → ((p1 → (p2 ∨ (p3 ∨ ((p2 ∨ True) → (p2 → False))))) ∧ p1)) ∨ False) ∧ p3) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p3 ∨ ((True → ((p5 ∧ p5) ∨ p1)) ∨ p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349455573805946631755330979092 : (p3 → (p5 → ((((((p3 → (p5 ∧ ((((False ∧ p5) ∧ False) ∨ (p3 ∧ False)) ∨ (p3 ∨ (True ∨ True))))) ∨ False) ∨ False) → p3) → p2) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_870814212279889145733216040149 : ((((False ∨ ((True → (((p4 ∨ p5) ∧ ((False ∨ p4) → p1)) ∨ (((p2 ∨ (p3 ∧ False)) ∧ (p2 ∨ True)) ∧ True))) ∨ (p1 → True))) → False) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ ((True → (((p4 ∨ p5) ∧ ((False ∨ p4) → p1)) ∨ (((p2 ∨ (p3 ∧ False)) ∧ (p2 ∨ True)) ∧ True))) ∨ (p1 → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262766487661291865973006779738 : (True ∧ (((True ∧ (p3 ∧ (p4 → p4))) ∧ (True ∧ ((p2 ∧ ((p2 → (p5 ∨ (False → True))) → False)) ∧ (p2 → (False → (p1 ∧ p4)))))) → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  let h8 := h3.left
  let h9 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h14 : (p2 → (p5 ∨ (False → True))) := by
    -- Implications on the right can always be decomposed.
    intro h15
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h17 := h13 h14
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149539869590775347809971514729 : ((p2 ∧ ((p2 ∨ (p1 ∧ ((((p5 → (p5 → p4)) → True) → (((p5 ∨ p4) → False) ∧ p2)) → p5))) ∨ p1)) ∨ (p4 ∨ ((p3 ∧ p3) → p3))) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137348614955539339205327299097 : ((p3 ∧ ((((True ∧ (p1 → p1)) ∧ (p3 ∧ p4)) ∧ ((p1 ∧ (False ∧ (True ∧ p3))) ∨ (p5 ∨ (p2 ∨ p5)))) ∧ p1)) ∨ ((p5 ∧ False) → p5)) := by
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
theorem thm_5_vars_793949214259382078518149732483 : (((True → (p5 → (True ∧ (p4 → (((((p3 ∨ p2) ∨ (True → (p1 ∨ p2))) ∨ True) ∨ ((False ∧ p1) ∨ (p4 ∨ p4))) ∧ (p2 ∧ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116162730372855009561178410657 : (((p5 ∨ (p1 ∧ True)) ∧ (p1 ∧ ((((((p2 ∨ p5) ∧ (False ∨ p4)) → p5) ∧ ((p2 ∨ True) ∧ (p4 → p5))) ∧ False) ∧ p4))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653734299664757902197442990399 : (((((((((p3 ∨ ((p3 ∧ (False → (True ∨ p3))) ∧ p1)) → p3) ∨ (True ∧ p3)) → (p1 ∨ p2)) ∨ (p4 ∧ p1)) ∧ p1) ∨ (p5 → p5)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_937318224604841633120636293574 : (((((p1 → (p3 → p3)) → (True → p2)) ∧ (p3 → (p5 → (((p5 ∨ p2) ∨ (p4 ∨ p3)) ∨ ((p2 → ((False ∧ False) ∧ False)) → p3))))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p1 → (p3 → p3)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704276460662850965467890702866 : ((((((p1 ∧ (p3 ∧ True)) → p3) ∧ (False → (p4 ∧ p3))) → (p1 ∨ ((p3 ∨ (True → (p2 ∧ (False ∧ (p3 ∧ False))))) ∧ (p1 → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41627997070606662828537908300 : ((((((p2 → p5) ∧ True) ∨ ((True ∧ p3) → p1)) → ((p5 ∧ (((p2 ∧ p5) ∧ p3) ∨ (p3 → False))) ∨ ((p3 ∧ p1) → True))) ∨ False) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172391823484701090124569321920 : ((((p1 ∨ (p2 ∧ p2)) → (p5 → p2)) → ((((p1 → p2) → p1) ∨ p2) ∨ False)) ∨ (True ∧ (True ∨ ((False ∧ ((p2 ∧ p3) → p3)) ∨ p4)))) := by
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
theorem thm_5_vars_117860511887192506015285712105 : ((p5 ∧ ((p4 ∧ (((((p3 ∧ p4) → True) ∧ p2) ∧ (p1 ∨ ((p1 ∧ p1) → (p3 ∨ (p1 ∧ (True → False)))))) → p3)) ∧ p5)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217901808825645230476627365823 : (((p3 → (p5 ∨ True)) → False) → ((((((True → p4) ∧ True) ∨ (p5 ∨ p3)) ∧ ((p1 ∧ p3) ∨ (p3 ∨ p3))) ∨ ((True ∧ p3) ∨ p1)) → p5)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h12 : (p3 → (p5 ∨ True)) := by
          -- Implications on the right can always be decomposed.
          intro h13
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h14 := h1 h12
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h17 : (p3 → (p5 ∨ True)) := by
            -- Implications on the right can always be decomposed.
            intro h18
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h19 := h1 h17
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h21 : (p3 → (p5 ∨ True)) := by
            -- Implications on the right can always be decomposed.
            intro h22
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h23 := h1 h21
          -- False on the left can always be used.
          apply False.elim h23
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h26 =>
          -- Conjunctions on the left can always be decomposed.
          let h27 := h26.left
          let h28 := h26.right
          -- One of the premise coincides with the conclusion.
          exact h25
        case inr h29 =>
          -- Disjunctions on the left can always be decomposed.
          cases h29
          case inl h30 =>
            -- One of the premise coincides with the conclusion.
            exact h25
          case inr h31 =>
            -- One of the premise coincides with the conclusion.
            exact h25
      case inr h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h33 =>
          -- Conjunctions on the left can always be decomposed.
          let h34 := h33.left
          let h35 := h33.right
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h36 : (p3 → (p5 ∨ True)) := by
            -- Implications on the right can always be decomposed.
            intro h37
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h38 := h1 h36
          -- False on the left can always be used.
          apply False.elim h38
        case inr h39 =>
          -- Disjunctions on the left can always be decomposed.
          cases h39
          case inl h40 =>
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h41 : (p3 → (p5 ∨ True)) := by
              -- Implications on the right can always be decomposed.
              intro h42
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h43 := h1 h41
            -- False on the left can always be used.
            apply False.elim h43
          case inr h44 =>
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h45 : (p3 → (p5 ∨ True)) := by
              -- Implications on the right can always be decomposed.
              intro h46
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h47 := h1 h45
            -- False on the left can always be used.
            apply False.elim h47
  case inr h48 =>
    -- Disjunctions on the left can always be decomposed.
    cases h48
    case inl h49 =>
      -- Conjunctions on the left can always be decomposed.
      let h50 := h49.left
      let h51 := h49.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h52 : (p3 → (p5 ∨ True)) := by
        -- Implications on the right can always be decomposed.
        intro h53
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h54 := h1 h52
      -- False on the left can always be used.
      apply False.elim h54
    case inr h55 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h56 : (p3 → (p5 ∨ True)) := by
        -- Implications on the right can always be decomposed.
        intro h57
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h58 := h1 h56
      -- False on the left can always be used.
      apply False.elim h58



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_947240420013080110170910964993 : ((((((p3 → False) → p3) → True) → ((((p2 → True) → (True ∨ ((p1 ∧ p2) → p4))) ∧ p2) ∧ (((True ∧ p3) ∧ (p4 → p2)) ∨ p5))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 → False) → p3) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716689843199588349262636186148 : (((((p4 ∨ p4) → (True ∨ p4)) ∧ (p5 ∧ (((p1 ∧ (p1 ∨ (((p5 → (True ∧ (p5 ∨ p5))) ∧ (True → p5)) → p2))) → p5) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157272286647937884197965911421 : ((((p4 ∧ (True → p1)) ∨ (((p5 ∧ (p5 ∨ p5)) ∨ (p1 ∨ p4)) ∨ ((p1 ∨ p4) ∨ p1))) → False) ∨ ((True ∨ ((p5 ∨ p3) ∧ p2)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305330959260908338766442641879 : (p1 ∨ ((((p2 ∧ (p5 ∧ (p5 ∨ (p5 ∧ p4)))) ∨ (((True ∨ (True ∨ p1)) ∨ p5) ∧ False)) → False) → (((p5 ∧ (p4 ∨ p2)) → False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241541550297843702325789761538 : ((False → p3) ∧ (((((p1 ∨ False) ∨ p4) ∨ (False ∧ p4)) ∨ p4) ∨ ((p3 ∨ (p5 → ((p3 ∧ p3) → (p2 ∨ p3)))) → (True → (p3 → True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49190096850022496716687525137 : (((((p5 → False) ∧ p4) ∧ ((p2 ∧ (p1 ∧ False)) ∨ ((p5 → ((False → p5) ∨ (p4 → (p1 ∨ False)))) ∧ p2))) ∨ ((p1 ∧ p3) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54757198131828225044354812071 : ((((p4 ∨ p4) ∨ (False ∨ ((True → p4) ∨ p1))) → ((True → p2) → (p5 ∨ (p1 → ((p5 ∨ (True ∨ (p1 ∨ p5))) ∧ (p4 → p2)))))) ∨ False) := by
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h7
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h11
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h12
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h19
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h20 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h21 := h2 h20
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h23
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h24
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h25 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h26 := h2 h25
        -- One of the premise coincides with the conclusion.
        exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148040445018797630534398052756 : ((((p2 ∨ True) → (((p5 ∨ p4) → ((p1 ∨ ((p3 → p1) → (p4 ∧ p5))) ∨ p4)) ∨ p2)) ∨ (p2 ∧ False)) ∨ ((p2 ∧ (False ∧ True)) → p5)) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142673275604717748285348117564 : ((p1 ∨ (((True ∨ (True → p3)) ∨ p4) ∨ ((p5 ∨ ((p3 → (p4 ∧ (False ∧ (p3 ∨ (p4 ∨ True))))) → p3)) ∧ p4))) → ((p2 ∨ True) ∨ False)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h7 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48342068270370825987091434848 : (((p2 ∨ (p1 → ((p4 → (p1 → (((((p4 → p3) → ((False ∨ False) → (p4 ∧ p5))) ∧ p2) ∨ p2) ∧ p1))) → p1))) → (True → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_956771386239919875423284009020 : (((((p2 → True) → True) → (((p2 → (p4 → (p4 ∨ ((p1 ∨ (True ∨ p1)) ∨ p5)))) ∧ False) ∧ (p4 → (p3 → (p5 ∨ (p1 ∨ p1)))))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 → True) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64364889792685605325772646890 : ((p1 ∨ ((((((False → True) ∨ ((p3 ∨ p4) ∧ p3)) → False) ∨ p5) ∨ ((p5 ∨ p5) → (p5 ∨ (p3 ∧ (False ∨ (p5 ∨ False)))))) ∨ p2)) ∨ p1) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260005100706200164923038570756 : ((p2 → True) → ((p3 ∧ (p3 ∨ ((False ∧ p2) → p5))) ∨ (p5 ∨ (False ∨ ((p4 ∧ ((p1 → ((True → p4) ∧ True)) → False)) ∨ (False → False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115938133348633470901194084594 : (((p5 ∧ (p5 → (False ∨ p3))) ∨ (((p4 → p4) ∧ p3) ∨ (p2 → ((p1 → False) ∨ (((False → (p3 ∧ p1)) ∨ p2) ∧ True))))) ∨ (False ∨ p5)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306632715311278829505524886884 : (p1 ∨ (True ∧ ((((p3 ∧ (True ∧ p5)) ∧ (True ∧ (p4 ∨ (p3 ∨ (((p2 → ((True ∧ p4) ∧ (False → True))) ∨ True) ∧ p3))))) ∧ True) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52054136869816311774855898270 : (((p3 → (((p4 ∨ ((True ∨ True) ∨ p3)) ∨ p2) → ((p3 → False) ∧ (p1 ∨ p5)))) ∨ (p4 ∨ (p4 → ((True ∨ (p2 ∧ p4)) ∨ p4)))) ∨ p4) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_17812145755411814395134058989 : (((((((p5 ∧ True) ∨ p5) ∨ ((p1 ∧ p5) → (((p1 ∧ p2) ∨ True) ∨ (p4 ∨ True)))) ∨ p2) ∧ p5) ∨ (p4 → ((p1 ∧ p3) ∨ p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150224793208980277755115355103 : ((p2 → (p1 ∨ (((((p2 ∨ p2) → p2) ∨ (((False → p4) → ((p4 ∨ p5) ∧ p3)) → p1)) ∨ p5) ∧ False))) ∨ ((p2 ∨ p5) → (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165797252971872325128905053930 : ((((p5 ∨ p3) ∧ p5) ∧ (True → ((False ∧ ((p2 ∧ p4) ∧ (False ∧ p1))) ∨ (p2 ∨ p1)))) ∨ ((((p1 ∨ p5) ∨ p3) ∧ False) → (True → False))) := by
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
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193233266441422249162557098039 : ((((p4 ∨ True) ∨ p3) ∧ ((p1 ∧ (True ∨ p3)) → p1)) → (True ∧ (((((p2 ∧ p4) ∧ (p3 ∧ p1)) ∨ p4) ∨ ((True ∧ p3) ∨ p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54713488072388134677947811965 : ((((((p5 ∧ p4) ∨ False) ∨ p4) → (p4 ∨ p3)) → (((p5 ∨ False) ∧ p1) → (((p1 ∧ (p4 ∨ (p2 ∧ p4))) ∨ True) → (p3 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51209292265887049325648534295 : (((((((p1 ∨ p3) ∨ False) ∨ (p5 → p2)) ∧ p1) ∨ (True ∧ (p1 → ((False → p1) → False)))) ∨ ((p2 ∧ ((False → False) → p3)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694205281114529421632794874902 : ((((((p4 → p5) ∧ (p4 ∨ False)) ∧ (((p3 ∨ p3) → (p1 ∨ p1)) ∨ p1)) ∨ (((p5 ∧ (p3 ∧ p1)) ∧ (False ∧ p4)) → (p1 ∨ p5))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749839496077510522056463153651 : (((True ∧ ((p3 ∨ ((p3 ∧ ((p3 ∨ p3) → ((p1 ∨ p1) ∧ (p3 ∨ True)))) ∧ ((p3 → ((p5 ∨ p3) → p2)) → (p4 ∧ p3)))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343313698194171122189122866021 : (p2 → ((p2 ∨ True) ∧ ((p2 ∨ p3) → ((((((p2 ∧ (p5 ∨ p4)) ∨ (p2 → (False → p4))) ∧ ((p3 ∧ p1) → p5)) → p3) → False) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219210953234194060912596229900 : ((False ∨ (p1 → (p2 → False))) → (True → ((((p5 ∨ p1) ∧ ((((p3 → p5) → (p1 ∧ p2)) ∧ p2) ∧ p4)) ∨ True) ∨ (p2 ∧ (False ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37720151472348404133428691071 : (((((((((p4 ∧ p3) ∨ p4) → ((True ∧ (p3 ∨ True)) ∨ p3)) ∧ p5) ∨ False) ∨ (True → (p5 → ((p2 ∧ p2) ∨ p3)))) → False) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344188824439719997049351172580 : (p2 → (p1 ∨ ((p1 ∧ (((False ∨ p1) ∧ p3) ∧ ((p1 ∨ p4) → p1))) ∨ ((p3 ∧ (False ∧ p1)) → ((((p3 ∧ p1) ∨ p3) ∧ p4) → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h2.left
    let h10 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h2.left
    let h15 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- False on the left can always be used.
    apply False.elim h16



