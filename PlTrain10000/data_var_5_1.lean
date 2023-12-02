variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313167830515983214944771187728 : (p3 ∨ ((((False → p5) → ((p1 ∨ p3) ∧ ((False ∧ p2) ∧ p5))) ∨ (((p3 ∧ (p2 ∧ (False ∧ (p1 ∨ p5)))) ∧ p3) → (p1 → False))) ∨ p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179622846587532551762042664635 : ((p4 → (((((p5 → p5) ∧ (True ∨ True)) ∧ p1) ∧ p2) ∧ (True → p3))) ∨ (((p1 ∧ (((False ∧ p4) → p5) ∧ True)) → p2) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138773456790796501266900602066 : ((((False → p2) ∧ ((p3 ∧ ((p1 → p5) → False)) ∨ ((True → p3) ∧ ((p1 → (p5 → (False ∨ p5))) ∨ p4)))) ∧ True) → ((p5 ∨ p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h14 := h10 h13
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h17 := h10 h16
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301097534547204019710781794521 : (False ∨ ((p4 ∨ ((False → (p3 ∧ (p4 ∨ p4))) → (p4 ∧ p2))) → (p4 ∨ ((p1 → ((True → p4) ∧ (p4 ∨ (p3 → p4)))) ∧ (False ∧ p2))))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (False → (p3 ∧ (p4 ∨ p4))) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h5
      -- False on the left can always be used.
      apply False.elim h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166583007598236989434421453128 : ((True → (((p1 → False) ∨ (p2 ∨ ((False ∧ p5) ∧ p5))) ∨ (p3 ∨ (True → (False → p2))))) ∨ (((((p5 → p4) ∨ True) ∧ p1) ∨ False) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114476302053902539175897031178 : ((((p5 → ((p3 → (((p3 → p1) ∧ (p3 → True)) ∨ p3)) → (p5 → (p4 → p3)))) → False) → ((False ∨ (p1 ∨ p4)) ∨ p4)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216765705784057663142482469839 : ((((p4 → p3) → p1) ∧ True) → (((p5 ∨ p3) ∨ (p3 → ((p2 → ((False ∨ False) ∧ p3)) ∨ p1))) → (p2 → (True ∧ (p3 ∨ (p4 → p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h1.left
      let h7 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h1.left
      let h11 := h1.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317882779056518474186272553634 : (p4 ∨ ((True ∧ ((False → (p5 → ((((p1 ∧ (p5 → p4)) ∧ (p4 ∧ p3)) → (True ∧ True)) ∨ False))) → (((p2 → p2) ∨ False) ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783885220966724426650823081737 : (((p3 ∨ ((p4 → (False ∧ p5)) ∧ ((p1 ∧ p5) ∨ (p4 → (((((p2 → (p1 → p1)) ∨ p4) → p3) → (p4 ∧ (p4 ∨ p5))) → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164469078678917527045879820338 : (((((True ∨ ((False ∧ (p2 → (p2 ∨ p5))) → ((p1 ∧ p4) ∧ p1))) → p3) ∨ p2) ∧ p2) ∨ (((True → (p1 ∧ p4)) ∧ p5) → (True ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142326839289769859514441399494 : ((p3 ∧ ((p4 ∧ ((((p5 ∨ p1) ∨ (False ∨ (p3 ∨ p4))) ∧ True) ∨ ((True ∨ (p4 → p5)) → p3))) ∨ (True ∧ p5))) → ((p2 ∨ p3) ∨ p4)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h5
          case inr h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h17
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57633988369099460664609620749 : ((((p4 ∧ p1) ∨ False) → ((p5 ∨ (False ∨ p5)) → (((((p1 → p2) ∧ p2) ∨ False) ∨ p2) → (((p1 ∧ p1) → p3) ∨ (True → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111627333092447377983888443193 : (((((p2 ∨ (p1 ∧ (((False → (p3 → (p4 → ((p4 ∨ p5) ∧ (p4 ∨ False))))) ∧ p3) → p5))) → (False ∧ p3)) ∨ True) ∨ p4) ∨ (True → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50619623450615782505141464942 : (((((p4 → p3) ∧ ((True ∧ True) ∧ (((p1 → p5) ∧ (p3 ∧ p3)) ∨ False))) ∧ ((False ∨ False) → False)) → ((p4 ∨ (p2 ∨ p1)) → p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h1.left
      let h21 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h20.left
      let h23 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h24.left
      let h27 := h24.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h28.left
        let h30 := h28.right
        -- Conjunctions on the left can always be decomposed.
        let h31 := h30.left
        let h32 := h30.right
        -- One of the premise coincides with the conclusion.
        exact h32
      case inr h33 =>
        -- False on the left can always be used.
        apply False.elim h33
    case inr h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h1.left
      let h36 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h37 := h35.left
      let h38 := h35.right
      -- Conjunctions on the left can always be decomposed.
      let h39 := h38.left
      let h40 := h38.right
      -- Conjunctions on the left can always be decomposed.
      let h41 := h39.left
      let h42 := h39.right
      -- Disjunctions on the left can always be decomposed.
      cases h40
      case inl h43 =>
        -- Conjunctions on the left can always be decomposed.
        let h44 := h43.left
        let h45 := h43.right
        -- Conjunctions on the left can always be decomposed.
        let h46 := h45.left
        let h47 := h45.right
        -- One of the premise coincides with the conclusion.
        exact h47
      case inr h48 =>
        -- False on the left can always be used.
        apply False.elim h48



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157258347023287149765605166800 : ((((((p5 ∨ True) → p4) ∧ p5) ∨ (p2 ∧ ((((p5 ∨ (p5 ∨ p4)) → False) → p4) ∨ p2))) → False) ∨ (p2 ∨ ((False ∧ False) → (p4 ∨ False)))) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165247745000590549610983991342 : (((p4 ∨ (((p5 ∧ (p3 ∨ True)) ∨ False) → (((p3 → p3) → False) ∨ True))) ∨ (p4 ∧ p5)) ∨ ((((True → p2) → False) ∧ (True ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87371862272506215911527384353 : ((((False → p4) → ((False → p2) ∧ p4)) ∧ ((((p3 → p5) → False) → ((True → ((False → True) → False)) ∨ (p4 → (p5 → p1)))) → False)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p3 → p5) → False) → ((True → ((False → True) → False)) ∨ (p4 → (p5 → p1)))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : (p3 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h8
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h11 := h3 h4
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64008204604564441081338215619 : ((False ∨ ((p1 ∨ ((p4 ∨ ((p5 ∨ (p3 ∧ (p4 ∧ (p4 ∨ (p2 ∨ (((p4 ∨ p1) → p5) → p1)))))) ∧ False)) ∨ p1)) ∧ (False → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227407173478843462929562046568 : (((p4 → p5) → p1) ∨ ((((False ∨ (p1 → ((False → ((p1 ∨ p3) ∨ ((p1 ∧ (False ∧ p1)) ∨ p1))) → p5))) ∧ p5) → (p1 ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204582785440395672973529887169 : ((((False ∧ p2) ∨ (p2 ∨ p3)) ∨ p4) ∨ (p4 ∨ ((False → True) → ((((p2 ∧ (p4 → p5)) ∨ p2) ∧ p2) ∨ ((False ∨ p1) → (p3 ∨ p1)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40741342481051091412411247201 : ((((((p1 ∨ p5) ∧ False) ∨ (((p3 → p1) → (((p3 ∨ p5) ∨ ((False → p1) ∧ p3)) ∨ p3)) → (False ∨ (True → p4)))) → False) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149224019780140832712271742624 : (((p3 ∧ p1) ∨ ((p5 ∨ (p4 → p1)) → ((p5 → ((False ∨ p5) → (False ∧ (p1 → False)))) → (p2 ∧ p4)))) ∨ (((True ∨ p5) ∧ p2) → p2)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112141837498108288094835020529 : (((p1 ∧ (((((((p1 ∧ p1) ∨ (p1 ∧ (False ∧ p2))) ∨ p4) ∨ ((p2 ∨ (p5 ∧ p1)) → p2)) → False) ∨ p5) → p4)) ∨ p4) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661572803396522541283745361467 : ((((((p5 → p2) ∨ ((p3 ∧ p5) ∨ (p3 ∧ ((((p4 ∧ (p4 ∨ True)) → False) ∧ p1) → p3)))) ∨ ((p2 ∧ False) ∧ p2)) → (p3 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656343134595026897867542198729 : (((((((True ∧ (p1 ∨ p1)) → (p5 ∨ ((p2 ∧ False) ∧ False))) ∧ p4) → (((False ∧ (p5 ∨ False)) → p3) → (p5 → p1))) ∨ (False ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_40039865532228875939584304790 : ((((((p5 ∨ True) → (p5 ∨ ((False ∨ (True → ((p1 → False) ∨ ((False → (p1 ∧ False)) ∨ (p2 ∨ p4))))) ∨ p3))) ∧ p5) ∧ p3) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303756257125978542750035195332 : (p1 ∨ (((((p5 ∨ p2) ∧ ((p3 ∨ ((p1 ∨ (p4 ∧ p3)) → (p3 ∨ (((p5 ∨ p2) → p3) → p5)))) → False)) ∨ (p4 ∨ True)) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_444000397716814401139078059595 : (((((False ∧ False) ∨ ((((((p3 ∨ p4) ∧ False) ∨ p3) ∧ p4) ∨ ((p5 ∧ p4) → p3)) ∨ ((True → True) ∨ p5))) ∨ (True ∧ (p5 → False))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152311371862306830403798295751 : ((((p2 → (p3 ∨ p3)) ∨ True) ∧ ((p3 → p1) ∨ (((p2 ∨ (False → p2)) ∨ (p4 → p4)) → (p1 → False)))) → (((p5 ∨ p4) ∨ True) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653032860566311056704710576158 : ((((True → (((p3 → (((True ∧ (p5 ∧ False)) → p3) → False)) ∨ ((p5 ∨ ((p1 → p4) ∧ p5)) ∧ (p3 → p5))) ∨ True)) ∧ (p5 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254585070236988556127460480126 : ((p3 ∧ p1) → ((((((p1 → p1) ∧ p4) ∨ ((p5 ∧ True) ∧ p1)) ∨ ((p3 → p1) → (p1 ∨ ((True → p3) → p3)))) → p4) ∨ (p3 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230688356196845436304118809790 : (((p4 → False) ∧ p4) → (False ∧ ((p3 → ((False → p4) ∧ (p1 → p4))) ∧ (p1 → ((False ∧ (((False ∧ p3) ∨ False) ∧ True)) ∧ (p1 → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h14 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h15 := h12 h14
  -- False on the left can always be used.
  apply False.elim h15
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
  have h18 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h17
  -- We have shown the premise of h16, we can now drive its conclusion.
  let h19 := h16 h18
  -- False on the left can always be used.
  apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h20
  -- Conjunctions on the left can always be decomposed.
  let h21 := h1.left
  let h22 := h1.right
  -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
  have h23 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h22
  -- We have shown the premise of h21, we can now drive its conclusion.
  let h24 := h21 h23
  -- False on the left can always be used.
  apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185541169384883736697642125864 : ((p3 ∨ (p3 ∨ (((p4 ∨ (p5 ∧ p2)) → (False → p5)) → p1))) ∨ (p3 → ((False ∨ (p3 ∧ (p1 → (p4 ∧ False)))) → (p1 → (p3 → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231669745909568573147635661290 : (((p1 ∧ False) → p1) → ((True ∧ (True → ((False → (True ∧ ((p1 ∧ (p2 ∨ p2)) ∨ (False ∨ p1)))) → p1))) → (((True ∨ p5) → p1) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (False → (True ∧ ((p1 ∧ (p2 ∨ p2)) ∨ (False ∨ p1)))) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h10
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51835604296154351872553304039 : ((((((p4 → (p3 → (p5 → ((p4 → (True ∧ p5)) ∨ p1)))) → p4) ∧ p5) ∧ True) ∨ (True ∧ ((False ∨ True) → ((p4 ∨ p2) → True)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327123110971540536352851417000 : (True → (((True → p3) → (p2 ∨ (False ∨ ((((((p1 → (p4 → p2)) → True) ∨ p1) ∨ (p4 ∧ (p4 ∧ (True → p5)))) ∧ False) ∧ p4)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632213113909645650272292998897 : (((((True ∧ (False ∨ (False ∧ ((((((p5 ∨ (p1 → p5)) ∧ (False ∨ False)) ∨ p1) ∨ (p3 → p5)) ∨ (True ∧ p3)) ∨ p3)))) → p5) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19669957872351860973062792321 : (((p3 ∨ ((((p5 → (((p1 → p2) ∨ False) ∨ p2)) ∨ False) → p2) ∧ (p2 → p5))) ∨ ((p4 → (True ∨ (True → (True ∨ p2)))) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_260247984409487068745837792977 : ((p2 → p3) → ((True ∧ (p3 ∨ ((p3 ∨ p5) → p3))) ∨ (p2 ∨ (((p5 → p3) ∧ ((p1 → p4) ∨ (True → True))) → (p1 ∨ (True ∨ p4)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729726797292989991806827569592 : (((((p2 → p5) ∨ p4) → ((p3 ∧ p1) ∧ ((p5 ∧ p1) ∧ (p5 → (((((p3 ∨ True) → p5) ∧ True) → p3) ∨ ((p4 ∧ p5) ∧ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257997457552624838417813605278 : ((p4 ∨ p1) → ((p1 → (p4 → ((False ∨ p3) → ((p2 → False) → (p4 → p2))))) → ((p1 ∧ (True ∧ False)) ∨ (p5 ∨ (p4 ∨ (p1 ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226161874808026512028716384916 : (((p1 ∨ False) ∨ p4) ∨ (p5 ∨ ((True ∧ (False ∨ p4)) ∨ ((p5 ∨ False) → ((p1 ∨ (p3 → (p1 → (((True ∨ p1) ∨ True) ∧ p5)))) → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311024521029547900408708751344 : (p2 ∨ ((False ∧ p5) ∨ ((((p2 ∨ (False → (p3 ∨ False))) ∧ p1) ∧ p2) → ((((p1 → p1) → p5) → (((False ∨ p2) ∨ p3) ∨ p2)) ∨ p5)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105902059566190282975331939866 : (((p5 ∨ (((False ∨ p3) ∨ ((((True → p1) → p1) → p2) ∨ True)) ∨ p3)) ∧ (p2 ∨ (True → ((p5 ∧ (p5 ∨ p4)) → True)))) ∧ (p4 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52614275408121930812741644247 : ((((False → ((p4 ∧ True) ∧ p4)) → ((((False → p5) ∨ p5) → p1) ∧ True)) ∨ (p4 → (((True ∧ p2) ∨ p5) → ((p1 ∨ p5) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172641327248504448742684068072 : (((False ∨ p3) ∧ (((p2 → p1) → ((False ∧ (p2 → True)) ∨ False)) ∨ (p4 ∧ p5))) ∨ (((False ∨ p5) ∧ (p3 ∨ (p5 → True))) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157052895299686594674136915930 : (((p2 ∧ (p2 ∨ (((p2 ∨ True) ∨ (p2 ∨ (((p1 → p2) ∧ p4) ∨ p1))) → (p3 ∨ p1)))) ∨ p3) ∨ (((True ∨ p4) ∨ (p4 → p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650179410736514978590959440991 : ((((((((p4 → ((p5 → (False ∨ False)) ∨ p2)) ∧ ((p1 → False) ∨ False)) ∨ p4) ∧ p4) ∨ (p3 ∨ (True ∨ (True ∧ True)))) ∧ (p4 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610598119134919004132051818635 : (((((((True → p4) ∨ (p3 ∨ (((p3 → True) → (((p3 → True) ∨ (p2 ∨ p4)) → (p1 ∨ p2))) ∨ p4))) ∨ (False → p4)) → p5) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_68826640964738245536244531285 : ((p4 → (((p1 → p5) ∨ p2) → (((p2 → (p1 → p3)) → (p1 ∧ p1)) ∨ (p3 → (p5 ∨ ((p3 ∧ p3) → (True ∨ (p1 ∧ p1)))))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218392385826824520889392983290 : (((True ∧ True) → (p4 → p1)) → (True ∧ (p2 ∨ ((True ∧ (p2 ∨ p3)) → (((False → True) → p1) ∨ (p3 → (p3 ∨ ((p4 → p1) ∧ p2)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623803537062115764846568831083 : ((((p1 ∨ (((p1 ∨ p1) ∧ p5) ∧ ((p1 → (((((((p2 ∧ (p1 ∧ p4)) ∨ True) ∨ True) ∨ p5) → p5) → p1) ∨ p2)) → p2))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_255422930856646668462050563475 : ((p5 ∧ p1) → (((((p3 ∨ p2) ∨ p4) ∧ ((p3 ∨ (p3 ∧ ((p3 ∨ (p2 ∨ ((False ∨ p3) ∨ p5))) ∧ (p5 ∨ p4)))) ∨ p2)) ∨ False) ∨ True)) := by
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
theorem thm_5_vars_319449675049159696337382105581 : (p4 ∨ (((((p2 ∨ p3) ∧ False) ∨ (((p2 → p4) ∧ True) ∧ p5)) ∨ p2) ∨ (p3 ∨ ((((p5 ∧ p2) → True) ∨ p4) ∨ ((p5 ∧ p4) ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_84828768973306599768846912781 : (((p2 ∨ ((((False ∨ p5) ∨ p2) → (p3 → (p4 → p1))) ∨ (False ∨ p1))) ∧ (((((p2 → p5) ∧ p3) ∨ p3) → (False ∨ True)) → False)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : ((((p2 → p5) ∧ p3) ∨ p3) → (False ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h5
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h14 : ((((p2 → p5) ∧ p3) ∨ p3) → (False ∨ True)) := by
        -- Implications on the right can always be decomposed.
        intro h15
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h20 := h3 h14
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h24 : ((((p2 → p5) ∧ p3) ∨ p3) → (False ∨ True)) := by
          -- Implications on the right can always be decomposed.
          intro h25
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h26 =>
            -- Conjunctions on the left can always be decomposed.
            let h27 := h26.left
            let h28 := h26.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h29 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h30 := h3 h24
        -- False on the left can always be used.
        apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184089469243794461613787321870 : (((((False ∨ p5) ∨ p3) ∨ (False ∨ (p1 ∨ (p1 ∧ p5)))) ∨ p2) ∨ ((p2 ∨ p2) → ((True → ((True → (True ∨ p2)) ∨ True)) ∧ (False → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118613129701010810860916713417 : ((p4 ∨ ((((p2 → ((True ∧ (p1 ∨ (p5 → False))) ∨ (p1 ∨ p4))) ∧ True) ∨ False) ∨ ((((True → False) ∧ True) ∨ True) ∨ p3))) ∨ (p5 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_48823830941003751486188879523 : (((p5 ∧ ((((True ∧ (p5 ∧ (((p3 → ((p1 ∨ p2) ∨ False)) ∨ p1) ∨ p2))) → p5) → (p5 ∧ True)) → p2)) ∧ ((p2 ∧ p1) → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53365236779469077351349517798 : ((((p1 ∧ (p2 → (p1 → ((p4 ∨ (p4 → True)) ∨ p1)))) ∨ p1) → ((p4 ∧ p2) ∧ ((p2 ∨ p4) ∨ ((False ∨ (p2 ∨ p3)) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165224932862910698355415391691 : ((((((p2 ∧ p2) ∨ p3) → True) → (((p3 ∧ p4) ∨ (p3 → p5)) ∨ False)) ∨ (p4 → True)) ∨ ((True ∨ (((p2 ∧ p2) ∧ True) → False)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62070036794480763818348049688 : ((p2 ∧ (False ∧ (((p2 → False) → (p4 ∧ (p1 → (p4 ∨ (p1 ∨ ((p5 ∧ (p3 ∨ p3)) ∨ (p5 → p1))))))) ∧ ((p3 → p1) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246543759288808017198954988391 : ((p5 ∧ p1) ∨ (p5 ∨ (((((p3 ∨ False) ∧ (p3 ∧ (((p3 → (((p3 ∨ p3) ∨ p5) ∨ True)) ∧ p4) → p4))) ∨ True) ∨ True) ∨ (p2 ∨ p5)))) := by
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
theorem thm_5_vars_391198706729592609673796656770 : ((((((p2 → False) → (p1 ∨ (p4 → p3))) ∨ (((p1 → False) ∨ p2) ∨ (True ∧ (((p1 → p1) → p3) → (False ∨ (p5 ∨ False)))))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_255328813737878338207888156242 : ((p5 ∧ True) → (((p4 ∨ p2) ∧ ((p4 → False) ∧ p2)) ∨ (((p4 → ((False ∨ (p4 → (((False ∧ p1) → False) ∧ True))) ∨ p5)) → False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114272196281834676593613736750 : (((((p1 ∨ ((p1 ∨ False) ∨ ((p4 ∧ p3) ∨ ((p5 → p5) ∨ (p1 → p4))))) ∧ True) ∨ p5) ∧ ((p2 ∨ p1) → (p1 → p3))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44753768397239905894408677607 : ((((((p3 → True) ∧ False) ∧ p4) → ((((True ∧ p1) ∧ False) ∧ (p1 → ((((p4 ∧ True) ∧ p4) ∧ p2) → p3))) ∧ (p2 ∨ p5))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585628880363225286413265741959 : ((((((True → ((True ∧ ((p3 ∧ (p3 → ((False → p3) ∧ p4))) → (p4 ∨ (p3 ∧ (p2 ∨ p3))))) → (p3 ∧ p3))) ∨ p3) ∧ p4) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346803306108624215555224124577 : (p3 → ((p5 ∨ (p5 ∧ ((p5 ∨ (True ∧ ((False ∨ (True ∨ ((p3 ∧ p5) ∨ p1))) ∧ p5))) ∨ (p1 ∧ p3)))) ∨ (p4 ∨ ((p4 ∨ p1) ∨ True)))) := by
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
theorem thm_5_vars_156892444640364727243206616588 : (((((p1 ∧ ((False ∧ p4) → p3)) → ((((p4 → p1) → (p3 ∧ p1)) → p1) → p5)) ∨ p1) ∨ p5) ∨ (p4 → (False → ((p3 → False) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256941005227709185165358731205 : ((p1 ∨ p5) → ((((True → ((False ∨ ((p3 ∧ (True → p1)) ∧ p1)) ∨ ((True ∨ p5) ∨ ((p4 → (p2 ∨ p2)) → p1)))) → p5) ∨ True) ∨ False)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184688332801551599814243460075 : ((((((p2 → p3) ∧ p2) ∨ p4) ∧ p4) → (p4 ∧ (False ∨ p5))) ∨ (p3 ∨ (p1 → ((False ∨ p2) → ((((p4 ∨ True) ∨ p2) → p3) → p1))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173148858134243006008807193190 : ((p3 ∨ ((True ∧ (((p3 ∧ p3) → True) ∧ False)) ∨ (p3 ∨ ((p3 ∧ p4) ∧ False)))) ∨ (False → (True → (True ∨ (p2 ∧ (p1 → (p5 → p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42200463120863545428191528022 : (((True ∧ (p1 ∧ ((((p4 ∨ (p1 ∧ (p1 ∨ p3))) ∧ p3) → (True → (p5 ∨ p1))) ∨ (((p1 ∧ p1) ∧ p2) → (p3 ∨ p2))))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55272822437665667644371183171 : ((((p1 → p4) → (True → (p2 ∨ False))) ∨ ((p5 → ((p2 → p5) → p5)) → (((p3 → True) → False) → (p1 → (p1 ∧ (p3 ∧ p2)))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h7
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792188155489480453409907313000 : (((True → ((((False ∨ (p3 → (True → (p5 ∨ p3)))) → p4) → (((p1 → False) ∧ (False → p3)) → p5)) ∧ ((p2 ∧ True) ∨ (p3 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300138336850845003979993848210 : (False ∨ ((p1 ∧ ((((((p1 ∨ True) → False) → p1) → p4) → (p5 ∧ p4)) ∧ ((((p4 ∨ p2) ∨ p5) → (p3 ∧ False)) → p3))) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352465675798140093524750225743 : (p4 → (((p4 ∨ p5) → False) → (p1 ∨ (((p3 ∧ (p3 ∧ p4)) ∧ (True → ((p2 → ((True ∨ (p1 ∧ (p1 ∨ p2))) → p2)) ∧ False))) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234528471100666784670136190333 : ((p2 → (p4 → p4)) → ((((p2 ∨ p2) ∨ p3) ∧ ((p4 ∧ ((p1 → (p1 ∨ ((p5 ∨ p2) → (False ∨ (False ∨ True))))) ∧ p2)) ∨ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65034720535326088153654383532 : ((p2 ∨ ((True → p3) → ((p2 ∧ (True ∨ ((p2 ∨ (p2 ∨ p5)) → ((p1 ∧ (p4 ∨ (p1 ∨ (p1 ∨ p2)))) ∨ (p1 ∧ p1))))) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113133185145859418943199077170 : (((p2 → (((p2 ∨ ((p4 ∧ False) ∨ p5)) ∨ ((((p5 ∨ p5) ∨ False) → p3) → ((p4 → p2) → (p4 ∧ p1)))) ∨ p2)) → p2) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48570064341055044379050133556 : (((((p4 → p3) ∨ (p5 → ((p2 ∨ p2) → (((p5 ∨ (p4 ∧ p1)) ∧ (p3 ∧ (True ∧ p5))) ∨ False)))) → p1) ∧ ((p2 ∧ p1) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149416024073721029785084212028 : ((True ∧ (((True ∧ (p2 ∧ (p5 → p4))) ∧ p1) ∨ ((((False ∨ (p5 ∧ (p3 ∨ p4))) ∧ p4) ∨ False) ∧ False))) ∨ (p1 ∨ (p2 → (False → p5)))) := by
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
theorem thm_5_vars_44291330299895866038359200161 : ((((((p3 ∨ True) ∧ ((p4 ∧ (p3 ∨ p5)) → p3)) ∨ (p4 ∧ (p3 ∨ (p4 ∨ True)))) ∧ (((p3 ∧ (p5 → p4)) ∨ p3) ∨ False)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111089485479402718054078444832 : (((((p2 → (p5 ∨ (p5 ∨ p4))) ∨ ((p5 ∧ False) ∨ (p5 ∨ p3))) ∨ ((p3 ∧ ((False ∨ p3) ∨ p4)) → (p2 ∨ False))) ∧ False) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65165584883079244719777273568 : ((p3 ∨ (((((p2 → p2) ∨ (False ∧ p5)) ∧ ((p3 → (True → p3)) ∧ (((p1 ∧ p3) ∨ p4) ∧ ((p1 → p2) ∧ p4)))) → p5) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115802445968841885004757971840 : (((((p5 ∨ p2) ∧ p2) → p4) ∧ (((((False ∨ False) ∨ (p2 ∨ p5)) ∧ (p4 ∧ (True ∧ ((p4 ∧ p1) ∧ True)))) ∨ p3) ∨ p1)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315167028884360035842931003154 : (p3 ∨ ((True ∧ ((p4 ∧ p3) ∨ (p4 ∧ p4))) → (p1 ∨ ((False → ((False ∧ False) → ((True ∧ p3) ∨ (p4 → p2)))) ∧ ((p1 ∨ False) ∨ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- False on the left can always be used.
    apply False.elim h16
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179069893454296471984054655629 : ((True ∧ ((((p1 → (p4 ∨ p1)) ∧ p2) ∧ p4) ∧ ((p3 → p4) ∨ p4))) ∨ (((False ∨ True) ∨ ((p3 ∨ p1) → True)) ∨ ((p5 → p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234557979391043797741778075806 : ((p3 → (p2 ∧ p5)) → (p4 ∨ ((p3 → (((p5 ∧ (((p4 ∧ p5) ∨ p1) ∧ (p1 ∨ p1))) ∨ (p2 → (True → True))) ∨ (p3 → p4))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179844062871528037359366165644 : (((p1 ∨ (p4 → (p5 ∧ (False ∧ (((p1 → p3) ∨ True) ∧ p4))))) ∧ p1) → ((p2 ∧ p2) ∨ (False ∨ (False → ((p1 ∨ (True → p1)) → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322273414094191385630972146245 : (p5 ∨ (((p2 → (False ∨ (p3 ∨ ((((((p1 → (False → p5)) → p4) ∨ p5) ∧ False) ∨ ((p2 ∨ True) ∨ (p4 → p3))) ∨ p3)))) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39032001577157850336413344545 : ((((p3 → p3) ∧ ((True → (False ∨ ((p1 ∨ p5) ∧ (p3 → (((False → (p3 ∨ ((p3 ∨ p1) → False))) ∧ p1) → True))))) → False)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255609690647562987990104209039 : ((p5 ∧ p4) → ((p3 → (((p5 → ((p3 ∨ (p4 ∨ ((((p1 → False) ∨ (p5 ∧ p4)) → (p2 ∧ False)) ∨ True))) ∧ p1)) → p1) ∨ p4)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262340714688258785010325571664 : (True ∧ ((((p4 → p3) ∧ (p5 ∧ p3)) ∧ ((((True ∨ p2) ∧ (((p5 ∧ (False → ((p1 ∨ True) ∧ p4))) ∨ p2) ∧ p2)) ∧ p2) ∧ p5)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615546379765221458917593170269 : ((((((p4 ∧ (p5 ∨ p1)) ∧ (False ∨ ((p3 ∧ (True ∧ (p5 ∧ (False → p5)))) ∨ p1))) → (p4 → (((False ∨ p1) ∧ True) ∨ False))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_46306548352338505818897971598 : ((((False → (p1 → (((p5 ∧ p3) ∨ (((p4 ∧ ((p1 → p1) → p5)) ∧ p3) ∧ p2)) ∨ p5))) → ((p1 ∧ True) ∧ p3)) ∧ (True ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56741648314821403871140857500 : ((((True → p1) ∨ p5) ∧ (p4 ∧ ((((((True ∨ p4) ∧ (p1 ∨ (p2 ∧ (p1 ∧ False)))) → p4) ∨ (False ∧ True)) ∧ (p5 → p4)) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217845951020038246028867038701 : (((p5 ∨ (p3 ∨ p3)) → False) → ((True → (True ∧ (((p1 ∨ p1) ∨ p5) → (((p2 → (False ∧ p1)) → (True ∧ (p4 ∨ p1))) ∨ p5)))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43810179142417265387131932547 : ((((p2 → (((p5 → (False ∨ ((p2 ∨ (p1 → (p1 → p2))) ∨ (True ∧ p4)))) ∨ (p1 ∨ ((p4 → p5) → p3))) → p3)) → p4) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255748037840059093581610186072 : ((True ∨ True) → (((p5 ∧ (p5 ∨ ((False ∨ p1) → (p3 → p1)))) → (p3 ∨ (p3 → p5))) ∧ ((((False → True) ∧ (p2 ∨ p1)) ∨ True) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      exact h5
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h16 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



