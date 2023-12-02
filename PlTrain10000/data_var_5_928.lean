variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689532755043732765938840284 : (((p5 ∧ (((True → (p1 ∨ ((p2 ∨ (p5 ∧ p1)) ∨ True))) ∨ p5) → p2)) → ((((p1 ∨ (p3 ∨ p1)) → p1) ∧ p2) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307203032184780982459999207749 : (p1 ∨ (p1 ∨ ((((True → p4) → ((p4 ∨ True) ∧ False)) ∧ ((False → p2) → p2)) ∨ ((False ∧ (False ∨ p2)) → (False ∨ (p3 ∧ (p3 → p1))))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172611616588230219402488547362 : (((p1 → (p2 → p3)) → (p4 ∨ ((p3 ∨ False) ∧ ((p2 → p5) ∨ (p5 ∨ p2))))) ∨ ((((p5 ∨ False) ∨ p4) ∧ p1) → (p4 ∨ (True ∨ True)))) := by
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
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204716553738286195802741596432 : (((True → (p1 ∨ (False ∨ p1))) ∨ p3) ∨ (False ∨ (((False ∨ p2) ∧ ((True → p3) ∧ True)) ∨ ((p3 ∧ p2) → (((p3 ∨ p3) → p5) → p2))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719268722718696509708889112741 : ((((p4 ∧ ((p4 ∨ p4) ∨ p3)) ∨ (((True ∨ p4) ∧ (p2 ∧ (p5 → False))) → (((p5 ∧ (p3 → (p1 → True))) ∨ (p4 ∨ p4)) ∨ p2))) ∨ p3) ∧ True) := by
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
    let h5 := h3.left
    let h6 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201050522493921357398841926547 : ((p4 ∨ (p5 ∨ ((False → (True ∨ False)) → p1))) → ((p3 ∧ p1) ∨ (((p5 → (p3 → (p2 ∨ ((p3 → p3) → True)))) ∨ p3) ∨ (p1 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206095633382036436841560859976 : ((p3 ∧ (True → (p1 ∨ (p2 → p2)))) ∨ (((((((p2 → ((True → p5) ∨ p3)) ∧ (True ∨ (True ∨ p2))) ∧ p1) ∧ p1) ∧ p1) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52582663993988711654354354974 : (((((p4 → (((p5 → True) → False) ∧ p1)) ∨ False) ∧ ((True → p4) ∧ True)) ∨ ((((p2 → (p5 ∧ (p4 ∧ True))) ∨ p2) → p3) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186769674950913386883808582751 : (((True ∨ ((p2 → p1) → (p3 ∧ p1))) → ((False ∨ p5) ∧ p2)) → ((((True → ((p5 ∨ False) ∨ (True ∧ p1))) ∧ (True → p2)) ∨ p1) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ ((p2 → p1) → (p3 ∧ p1))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (True ∨ ((p2 → p1) → (p3 ∧ p1))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- One of the premise coincides with the conclusion.
  exact h11
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h12 : (True ∨ ((p2 → p1) → (p3 ∧ p1))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h12
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117670562696084880337687866825 : ((p3 ∧ ((((((p1 ∨ (p5 → p3)) ∨ False) ∧ (False → False)) ∨ p4) ∨ p4) ∧ (((False ∧ (p1 → p2)) ∨ (False ∧ False)) ∨ p4))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178145532519769354656658957807 : ((((True ∨ (p5 ∨ p2)) ∧ (((False ∧ (p4 ∧ False)) → p5) → p2)) → p4) ∨ ((False ∧ p1) → (((p3 → (True ∧ p4)) ∧ (True ∧ p5)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65431101055090311505405063196 : ((p3 ∨ ((False ∧ p4) ∧ (True → (((p5 → True) → p3) ∧ ((False ∧ p2) → ((p5 → p4) ∧ (p3 ∧ ((p3 ∧ False) → (p1 → True))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304011110457270721149256507154 : (p1 ∨ (((p5 → p5) → ((((((p4 ∧ p4) ∨ ((((p2 ∧ (p3 ∨ (p1 ∨ p3))) ∨ p1) ∧ p5) ∧ p4)) ∨ True) → p1) → p5) ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207159505076885370048016861331 : (((p3 → ((p5 ∧ p3) → p3)) ∧ p1) → ((True → p2) → ((p5 → (p3 → (((p1 → ((p5 ∧ p2) → (p4 ∧ p4))) ∨ p1) ∧ False))) ∨ True))) := by
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
theorem thm_5_vars_152459173197546238430069471039 : (((False ∨ (p5 → p5)) ∧ (p2 ∨ (p1 → ((p3 ∧ p1) ∧ (False → (p5 ∧ ((p1 ∨ (p1 → p3)) ∨ p2))))))) → (False ∨ ((p1 ∧ p4) ∨ True))) := by
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
    cases h3
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219289503262884498152824713311 : ((p2 ∨ ((p3 ∨ True) ∧ p5)) → ((True ∨ True) → (((p2 ∧ p4) ∨ (((p3 ∧ True) ∨ p1) ∧ ((p4 ∧ p1) ∧ (p3 ∧ p5)))) → (p2 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
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
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h19 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h20 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h23.left
      let h28 := h23.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h27.left
      let h30 := h27.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h28.left
      let h32 := h28.right
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h34 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h34
        case inr h35 =>
          -- Conjunctions on the left can always be decomposed.
          let h36 := h35.left
          let h37 := h35.right
          -- Disjunctions on the left can always be decomposed.
          cases h36
          case inl h38 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h39 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h40 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h41 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h41
        case inr h42 =>
          -- Conjunctions on the left can always be decomposed.
          let h43 := h42.left
          let h44 := h42.right
          -- Disjunctions on the left can always be decomposed.
          cases h43
          case inl h45 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h46 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h47 =>
      -- Conjunctions on the left can always be decomposed.
      let h48 := h23.left
      let h49 := h23.right
      -- Conjunctions on the left can always be decomposed.
      let h50 := h48.left
      let h51 := h48.right
      -- Conjunctions on the left can always be decomposed.
      let h52 := h49.left
      let h53 := h49.right
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h54 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h55 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h55
        case inr h56 =>
          -- Conjunctions on the left can always be decomposed.
          let h57 := h56.left
          let h58 := h56.right
          -- Disjunctions on the left can always be decomposed.
          cases h57
          case inl h59 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h60 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h61 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h62 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h62
        case inr h63 =>
          -- Conjunctions on the left can always be decomposed.
          let h64 := h63.left
          let h65 := h63.right
          -- Disjunctions on the left can always be decomposed.
          cases h64
          case inl h66 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h67 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149226217973404207798658211443 : (((p3 ∧ p5) ∨ ((p1 ∨ ((p3 ∨ ((p2 → p1) → ((True ∧ True) ∨ ((p4 → p5) ∧ p5)))) → False)) ∧ False)) ∨ (p5 → ((p4 → p5) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248208880941750774681242619129 : ((p2 ∨ p1) ∨ (((False ∨ (((p1 ∨ (p5 → False)) ∧ True) ∨ False)) ∧ (p2 → (((True ∧ True) ∨ p2) → ((p2 → True) ∨ p5)))) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51869427858848886815593091127 : ((((((True ∧ p2) ∧ p1) ∧ ((True ∨ p3) ∧ (p4 ∧ (p4 ∨ (p5 ∨ True))))) ∨ p5) ∨ (p2 → (((False ∨ p4) ∧ False) → (p2 → False)))) ∨ p1) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111094364204762488086109785972 : (((((((p2 → ((p4 ∨ p1) ∨ p2)) ∨ p5) ∧ (p3 → p4)) → p1) → ((p2 → ((False ∨ p5) ∨ p4)) ∨ (p1 ∨ p5))) ∧ p1) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156897304644367735383225540654 : ((((p2 ∧ ((((p3 ∧ (p1 → ((p4 → p4) ∨ (p4 ∨ False)))) → p1) ∧ True) → p1)) ∨ p4) ∨ p3) ∨ ((p5 → (p2 ∧ p4)) → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137519979842551650998053798209 : ((p5 ∧ ((p1 ∧ p5) ∧ ((((((((p4 ∨ p1) ∧ True) → p2) ∨ (p3 → p5)) ∨ p3) ∧ (p5 → p1)) ∧ p5) ∧ p1))) ∨ (p3 ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158175817495993174922629456687 : ((((True ∨ False) ∨ (p1 ∧ True)) → (((True → ((p4 → (p5 → False)) → p1)) → (p2 ∨ p3)) ∨ p5)) ∨ (((False → p2) ∨ p5) ∨ (p2 → p3))) := by
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
theorem thm_5_vars_121764399814373643491276894223 : (((((p3 → p4) ∨ (False ∧ p4)) → (((p4 ∧ ((p2 ∧ p5) → (p3 → p1))) → p2) ∨ (True ∨ (p5 ∧ (p5 → p2))))) → False) → (p5 ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 → p4) ∨ (False ∧ p4)) → (((p4 ∧ ((p2 ∧ p5) → (p3 → p1))) → p2) ∨ (True ∨ (p5 ∧ (p5 → p2))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734978748546429980968511210970 : ((((p2 ∨ p5) ∧ (((p4 → True) → (p2 ∧ p2)) ∧ ((p4 ∨ ((p4 ∨ False) ∧ ((p4 → (True → p3)) → False))) ∨ (p2 ∧ (p2 ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199233956421178416446896581212 : (((True → (p5 ∨ (False ∧ (False ∨ p4)))) ∧ p5) → ((p4 ∨ (p3 ∧ ((False ∨ (p5 → p3)) ∧ True))) ∨ ((p2 → p3) ∨ (p2 → (True ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156924829175548118146382167001 : ((((p1 ∨ ((p5 ∧ p3) ∨ (p2 ∧ (((p4 → p4) ∨ (p2 ∨ p4)) ∨ (p1 → p3))))) → p5) ∨ p3) ∨ ((True → True) ∨ (p4 ∧ (p1 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669114317800436468306262639527 : ((((((((p4 ∨ (p5 → p5)) ∨ p5) → (((True ∨ p1) ∧ False) → p2)) ∧ ((p3 ∨ (False ∨ False)) ∧ p3)) → p4) ∨ (p1 ∧ (p3 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50091247916909225433033036354 : (((p2 ∧ ((p4 → (False → p2)) ∧ (p1 → ((p3 ∨ (p2 → p5)) ∧ (p2 ∧ ((True ∧ p4) ∨ True)))))) ∧ ((False → p1) ∧ (p4 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134843049920257788756414099710 : (((p4 ∨ ((p4 ∧ (((p3 ∧ True) ∧ (p1 → ((p4 → ((p2 ∨ p4) ∨ (True → p2))) ∧ True))) → p1)) ∧ p4)) → p3) ∨ ((p1 ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134176440439688318826114593123 : ((((((p2 ∧ False) ∨ True) → (p3 → ((True → (p4 ∨ p4)) ∨ (p2 ∨ True)))) → (((p2 ∨ p5) ∧ p3) ∧ p3)) ∨ True) ∨ (True ∧ (False → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50194757796823157156845083066 : ((((p1 ∨ ((((((((p2 ∨ (p4 ∨ p5)) ∨ p1) → p5) → p2) ∨ p1) ∨ p3) → p1) ∨ p2)) ∧ False) ∨ (True ∨ (True ∧ (False ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304283012408975440440664478567 : (p1 ∨ ((((p2 → (False ∨ ((True ∧ (False ∨ (p2 → (p1 → p2)))) ∧ (False → p2)))) → (p5 ∧ (p3 ∨ True))) ∧ (p3 → (p3 ∧ p2))) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → (False ∨ ((True ∧ (False ∨ (p2 → (p1 → p2)))) ∧ (False → p2)))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h4
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304766230121809984963530827970 : (p1 ∨ ((p4 ∧ ((p1 → ((p5 ∧ (p4 ∧ False)) → p5)) → ((((p4 → ((p5 ∨ p4) → (p5 ∧ p5))) → p2) → p5) ∧ True))) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654014828367133204038730927558 : (((((p1 ∨ ((((((True ∧ ((p2 → p1) ∧ p5)) ∧ p5) ∨ (p1 → p4)) ∧ (True ∧ (False ∨ p2))) ∧ p1) ∧ True)) ∧ p3) ∨ (p1 ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124304320944043574273802135134 : (((((p2 ∨ (p3 → p4)) → True) → (p1 ∧ False)) ∧ ((((p3 ∧ (False ∧ p1)) ∧ p2) ∨ (p2 ∧ p4)) → ((p2 → p1) ∧ False))) → (True ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p2 ∨ (p3 → p4)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134282255955575996228377638648 : ((((p2 ∧ p4) ∨ ((p1 → (p4 → (p5 → (p5 → (p4 ∧ ((p5 → p2) ∧ p3)))))) ∧ (p4 ∧ (True → p3)))) ∨ p4) ∨ (p3 → (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313155087679125212214751189839 : (p3 ∨ ((((p2 → (p1 → (p2 ∨ (p2 ∨ False)))) ∧ ((p2 ∧ p4) ∧ p5)) ∧ (p1 → ((((p4 ∨ False) ∨ p2) ∧ (p5 ∨ p3)) ∨ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324512740065567623362069280713 : (p5 ∨ ((p5 ∨ ((True → p5) ∨ p1)) ∨ (False ∨ (p3 → (p3 ∧ (((True ∨ ((p2 ∨ (False ∨ p1)) ∨ (p1 ∧ (p5 ∧ False)))) ∨ p1) ∨ p2)))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115077307142250681953199433679 : (((True ∧ ((((p3 ∧ False) ∨ (p4 ∨ (p3 ∨ p1))) → p2) → p4)) ∨ (p5 → (False ∨ (((False → True) → (p2 ∧ p3)) → p5)))) ∨ (False ∧ True)) := by
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
theorem thm_5_vars_685942067268915592745857552207 : ((((((True → (p5 ∧ ((p3 ∧ p3) ∧ p4))) → ((p2 ∧ p2) → (p4 → p4))) ∧ (p5 ∧ p5)) → (p5 ∧ (p3 ∨ (p2 → (p2 ∧ True))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639739534766687851729756767713 : (((((p3 → (p5 ∧ p4)) ∧ (True ∨ (p1 → (((p2 ∨ (p1 ∧ False)) ∧ p1) ∧ ((p4 → p1) ∧ ((True → (p4 ∨ p4)) ∨ True)))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197294537787992579815140075899 : ((((p4 ∧ (p4 → True)) → (p3 → p1)) → False) ∨ (p1 → (p4 ∨ (p5 → (((((p3 ∨ p1) → p5) ∨ p4) → p1) ∧ ((False ∨ p4) ∨ p5)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118487331893421750011379581244 : ((p3 ∨ (((p1 → (p4 → (p4 ∧ ((False ∨ p4) ∨ False)))) → (((True → p2) ∧ (True ∨ p5)) → p4)) ∨ (False → (p2 ∧ p5)))) ∨ (True → p2)) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336575630991557686911119963071 : (p1 → (((((p5 → p2) → (p5 ∨ ((True ∧ p4) → (False ∨ ((p3 ∧ p4) → ((False → False) → ((p5 ∧ p3) ∧ p5))))))) ∨ True) → False) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p5 → p2) → (p5 ∨ ((True ∧ p4) → (False ∨ ((p3 ∧ p4) → ((False → False) → ((p5 ∧ p3) ∧ p5))))))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178667188287531785054377418492 : ((((False ∨ p2) → (False ∨ p4)) ∧ ((p1 → ((p3 → p5) ∧ False)) ∨ p4)) ∨ ((p5 ∧ ((p1 ∨ (p2 → True)) ∨ (True ∨ p1))) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232103601759402910541462018410 : (((p5 ∨ False) → p2) → (((True ∧ (True → p2)) → ((p1 ∨ p3) → p4)) ∨ ((p1 ∧ p5) → ((p3 ∨ ((p4 → p2) ∨ (p5 ∧ p5))) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : (p5 ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h2.left
      let h12 := h2.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h13 : (p5 ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h14 := h1 h13
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h2.left
      let h19 := h2.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h20 : (p5 ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h21 := h1 h20
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207869034458003347295246582617 : ((((p1 → p3) ∨ p5) ∧ (p5 → p1)) → (p5 → (p1 ∧ (((((False ∧ p5) ∧ ((((p2 ∧ False) → True) ∨ p1) → p3)) ∧ p5) ∧ p2) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h14 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h15 := h12 h14
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h17 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h18 := h12 h17
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187686307239467868781842241842 : ((False → ((p1 → ((p2 → ((True ∧ p4) → p2)) → p2)) ∧ p1)) → ((((p2 → False) ∨ ((True → p3) ∧ (p1 ∨ p3))) → p1) ∨ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204355527905558403421361140475 : (((p1 ∨ ((p4 ∨ p5) ∨ False)) ∧ p4) ∨ ((((((False → (False ∨ False)) ∧ (p3 → p3)) ∧ (p5 ∨ True)) ∨ True) → (False ∧ (p5 ∧ p1))) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((False → (False ∨ False)) ∧ (p3 → p3)) ∧ (p5 ∨ True)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133810508836472403370038507987 : ((((p1 ∨ p4) ∧ (p2 → ((((((p4 → ((True ∧ False) → p3)) ∨ True) → p4) → (p4 → p4)) → True) → p5))) ∧ p4) ∨ ((False ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319814460924723411795239293534 : (p4 ∨ (((p5 ∨ (p2 ∨ False)) ∨ True) ∧ (((p2 → ((p1 ∨ ((((p1 ∧ (p4 ∧ p2)) ∧ p4) ∧ (p5 ∨ p2)) → p2)) ∧ p2)) ∨ p4) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h11 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165739450066780703884910245750 : (((((True ∧ p3) ∧ p3) → p5) ∨ (p4 ∧ ((p3 ∧ p1) ∨ (((False → p3) → p2) ∧ p4)))) ∨ (True ∧ (((False ∧ (p2 ∨ p4)) ∨ p5) ∨ True))) := by
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
theorem thm_5_vars_39755380764589586078676834952 : (((True → ((((p2 → p1) ∨ ((p1 → (p5 ∨ False)) ∧ p3)) ∨ (True ∧ (False ∨ (((p2 ∧ p2) ∧ (p2 ∨ p1)) ∧ p1)))) → p3)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219553212064505085464269692064 : ((True → ((p1 ∨ p3) ∧ False)) → (p1 ∧ (p2 ∧ (((p5 ∨ True) → (True → (p5 ∧ ((p2 ∧ (p4 → (True ∧ p2))) → True)))) → (p2 ∧ True))))) := by
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64005518481184896124189828938 : ((False ∨ ((((p1 → p5) → p5) ∧ ((p4 ∧ True) → (p5 ∧ ((p3 ∧ (((p2 ∨ (p1 → p2)) ∨ p1) ∨ False)) → False)))) ∧ (False ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744122240078464918641122441464 : ((((p1 ∧ True) → (p2 ∨ ((p3 ∨ p5) → (p5 ∨ (p4 ∧ (p5 ∨ ((p2 → False) → ((((p5 ∨ p2) ∨ (False ∧ True)) → p2) ∨ p4)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225184419372399102122447202409 : (((p4 ∧ p2) ∧ True) ∨ ((((p3 ∧ ((p5 ∨ p1) ∧ ((p5 ∧ (p4 ∧ (p3 ∨ p4))) ∨ (False ∨ p5)))) ∨ (p2 ∨ (p1 ∨ p3))) ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710435045270201806437759492308 : ((((((False ∧ p1) → (p4 → p4)) → p1) ∧ (((((False ∧ p3) → p1) ∧ (p5 → p5)) → (True ∨ (p2 ∨ ((False ∨ p5) ∧ p1)))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323475655804046979098595889430 : (p5 ∨ ((((p5 ∧ (((p2 ∧ ((False ∧ p2) ∨ (p2 ∧ p1))) ∨ (p1 → p3)) → p1)) ∨ ((p1 → p1) ∨ p1)) ∨ p2) ∨ ((p1 ∧ p5) ∧ p4))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175315635380145753966604834465 : ((p4 ∨ ((p2 → ((p5 ∧ ((p3 ∧ p1) ∧ (p3 → p4))) ∧ (p3 ∧ p1))) → p5)) → (((((p1 ∧ p3) → p2) → p3) ∨ (p3 → p2)) ∨ True)) := by
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
theorem thm_5_vars_61558841665322073497793537827 : ((p1 ∧ (((((p1 → (p2 → True)) ∨ True) ∧ p1) → p4) → (((True ∨ (p3 ∨ (p3 → ((p4 ∧ p5) ∨ True)))) ∨ (p1 ∨ p4)) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348802658954888908235305977051 : (p3 → (p1 ∨ (((True ∧ (((((((p2 ∧ (True → True)) ∨ p4) ∧ p5) → False) ∨ p4) ∨ p5) ∨ p1)) ∨ (p4 → True)) ∧ (p4 → (False → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135443099561517408673835787697 : (((((p1 ∧ (((p1 → (p3 → p2)) ∨ p1) ∨ (p1 ∨ (p5 ∧ p2)))) ∨ (p3 ∨ p5)) ∧ p1) → (False ∨ (p1 ∨ p1))) ∨ ((False ∨ p1) ∧ p4)) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62100841147710551554122481741 : ((p2 ∧ (p5 ∧ (p1 ∨ (((False → False) ∨ False) ∧ (((p1 ∧ ((p5 ∨ p4) ∧ (((p4 → True) ∧ False) → p5))) → (p5 ∧ False)) ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218468502721063352458142293463 : (((True ∨ True) → (p4 ∧ p3)) → (((p2 → (p4 ∨ (((p5 ∧ p5) → (p1 ∧ p3)) → p3))) → ((True ∨ p3) → (p5 ∨ p2))) → (p5 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p2 → (p4 ∨ (((p5 ∧ p5) → (p1 ∧ p3)) → p3))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h3
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328091679786808214135416473684 : (True → ((((p1 ∨ (((p2 ∨ (((p1 ∧ (p1 ∧ p3)) → p4) ∨ (p4 → True))) ∨ (False ∧ p5)) ∧ p5)) → p4) ∧ False) ∨ ((p5 ∧ p1) → p5))) := by
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
theorem thm_5_vars_229162710297808741931405789574 : ((True → (p2 ∨ p2)) ∨ ((((True → False) ∨ False) ∨ (True ∧ (p5 ∨ p5))) ∨ (((True ∨ ((p2 → p2) ∧ (True ∧ (p4 ∨ p4)))) ∨ p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791582899549675907787644939401 : (((True → (((p2 ∨ ((p3 ∧ p3) → ((p2 ∨ (((p2 ∨ (p5 ∨ (((p1 → p2) → p1) ∧ p3))) ∨ False) ∨ p2)) → p4))) ∨ True) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49018256278489763455142971692 : (((((((p4 → (True ∨ p2)) ∨ ((((p4 ∨ (p2 ∧ p1)) ∨ p2) ∧ p4) → p2)) → p1) → (p4 ∨ p2)) → p4) ∨ (False → (True ∧ p5))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158357330110271090800251272516 : (((False ∨ p2) ∧ (p4 ∧ (((p5 → p5) → ((False ∨ p2) ∧ (((p1 ∨ False) ∧ p1) ∨ p4))) ∧ p3))) ∨ (p3 → (((p1 → p1) ∧ p2) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310407784644051120418593504255 : (p2 ∨ ((p3 ∨ (p4 → ((p2 → p5) → (p3 ∧ False)))) ∨ (p3 → (p3 → ((True ∨ ((p2 → ((p2 ∨ p3) → p3)) → (True ∨ p5))) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215243545231415736810948073567 : ((False ∧ ((False ∨ p5) → p4)) ∨ (((p2 ∧ p3) → p1) → ((((p5 ∧ (p1 ∨ p1)) ∧ False) → (False ∨ p5)) → ((p5 ∧ p4) → (p1 → p1))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734289353017020567929083924408 : ((((False ∨ p2) ∧ ((((p1 ∧ p5) ∧ True) ∧ (p3 ∨ (p4 ∨ ((p5 ∨ True) ∧ ((p1 → p3) ∧ (False → ((p3 ∨ p1) → p1))))))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760388391117504148674757729640 : (((p2 ∧ ((p2 → p5) → (((p5 → (((p4 → (p1 ∧ (p1 → ((p3 → ((True ∧ p3) → p2)) ∨ p5)))) → p3) → p1)) → p3) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208940504679610993371532172909 : ((p5 ∧ (p4 → (True ∧ (p5 ∧ False)))) → (p1 → ((p5 ∧ p4) → (True ∧ (p2 ∧ (((p5 ∧ (False → p2)) ∨ False) → (p3 ∨ (p2 ∧ p3)))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h3.left
    let h17 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h1.left
    let h19 := h1.right
    -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
    have h20 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h19, we can now drive its conclusion.
    let h21 := h19 h20
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- We need to get the right conjuct of h22 based on <expert-advice>.
    let h23 := h22.right
    -- False on the left can always be used.
    apply False.elim h23
  case inr h24 =>
    -- False on the left can always be used.
    apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200823194114897749245736712553 : ((p5 ∧ (False ∨ ((p5 ∧ p3) → (p2 → False)))) → (p3 ∨ (p1 → ((((True → p4) → p2) ∧ (p4 → ((p4 ∨ True) ∨ p2))) ∨ (p3 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319015635529636621036209766765 : (p4 ∨ ((p1 ∨ ((False ∨ (False → p3)) ∨ ((p1 ∧ (((p3 → p1) → (True ∧ False)) ∧ p5)) ∧ (p5 ∧ p3)))) ∧ ((p5 ∨ (p4 ∨ True)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185700973682490207921437241166 : ((p2 → ((False ∧ ((p2 ∨ (False → (False → p4))) ∨ False)) ∨ p3)) ∨ ((((p1 ∧ ((True → p4) → (p4 → p4))) ∨ p2) ∧ p1) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596711621704840034248969756216 : ((((((True → p4) ∨ (p1 ∧ (p2 ∨ True))) ∧ (((p3 ∧ (p1 ∧ (((True ∨ p1) ∨ (p3 ∧ p2)) → False))) ∧ (p5 ∨ p5)) ∨ False)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768814742575284508356025135825 : (((p5 ∧ ((p5 ∧ (p3 ∧ ((p4 ∧ p4) → p3))) ∧ ((True → p5) ∨ ((((True → False) → p3) ∨ (p2 → p5)) → ((True → p3) → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51302411933192612407341515535 : (((False ∨ (p5 ∨ ((((p4 ∧ True) → (p3 ∨ (p1 ∧ (p5 ∨ p2)))) → True) → (True → p2)))) ∨ ((True → (False ∧ p2)) → (p1 ∨ p1))) ∨ p5) := by
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45912356669340186527048984542 : (((p4 → ((p2 → (True ∨ (p3 → (p2 ∨ ((p1 ∨ p3) → (False → (p2 ∧ p5))))))) ∨ (((p4 → p1) ∨ p1) → (True → p4)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116313258583618078815618781438 : (((p4 → (False ∨ p5)) ∨ (p3 → ((((((p1 → (p3 → True)) ∧ p1) ∧ True) ∧ p1) ∧ ((p5 → p1) ∨ (True ∧ False))) ∨ p2))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686478977733109752161843189240 : ((((((p4 → False) ∨ p5) ∨ (True ∧ ((p2 ∨ (p5 → p4)) → (p5 → (p4 ∨ (p1 ∨ True)))))) → (p5 → ((p4 ∧ (p1 ∧ p4)) ∨ p5))) ∨ p5) ∧ True) := by
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
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
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150052821643920315626434665970 : ((True → (((p2 ∨ True) ∧ (p1 ∨ ((((((p2 → False) ∧ p3) → p2) → True) ∧ p3) → (p2 ∨ p5)))) ∨ p2)) ∨ (True ∨ ((False ∨ p1) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_222536607105313891722067159319 : ((True ∧ (False ∨ True)) ∧ (p2 → ((((((((True ∨ p4) ∨ p2) → p4) ∧ (p1 → p5)) ∧ ((p5 ∨ p4) ∧ False)) ∨ (p2 ∧ True)) ∨ p3) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594288530864654375626452748760 : (((((((p5 ∨ (p4 ∨ True)) ∨ ((((p1 ∧ p3) → True) ∧ p4) → (p1 ∨ p2))) ∨ p5) ∧ ((p5 ∧ (False → (True ∨ True))) ∧ p3)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319536661917376755667784639615 : (p4 ∨ (((p3 → ((True ∧ p1) ∨ ((p3 ∨ p5) ∧ p4))) ∧ p1) ∨ (((p5 → (((p4 → True) ∨ True) ∧ (p3 ∨ (p2 → True)))) ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607936914692196206674626108494 : (((((p1 → (False ∨ (p3 → ((p2 ∨ (((p1 ∨ (p5 → False)) ∧ p5) → (((False ∧ p4) ∧ p4) ∧ (True ∧ False)))) ∧ p2)))) ∧ p2) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54075477916325889194524272290 : ((((p1 ∧ True) ∧ (p3 ∨ ((p4 ∧ p3) ∨ (p2 ∧ True)))) → ((p4 ∧ True) ∧ ((p2 → (((p2 ∨ p5) ∧ p1) ∨ (p2 ∨ p2))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635132135335908120640952695942 : ((((((p3 ∨ ((p5 ∧ True) → p5)) ∧ (((p5 ∧ ((p2 ∧ False) ∧ p4)) ∧ p2) ∨ ((p5 ∨ p5) → p5))) → ((p5 → p5) → p1)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37367858854019958865725204038 : (((((p5 ∧ (((p5 → (p1 → p1)) → ((p3 ∧ p2) → (p1 ∨ p5))) ∨ ((p5 ∧ ((p3 ∨ False) ∧ p2)) → False))) ∨ p2) ∨ p5) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781363185866828880773193371930 : (((p2 ∨ (p2 ∧ ((((p3 ∨ False) ∧ (p2 → ((False → (p4 ∧ p5)) ∨ p5))) ∨ ((p4 ∧ True) ∧ (p4 → p5))) ∨ (p2 ∨ (False → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231558050075884179977442214472 : (((p5 → p1) ∨ p2) → ((p1 → (((((True → (p1 ∨ p3)) ∧ (p1 ∨ p5)) → (p1 ∨ True)) ∧ (False ∨ p3)) ∧ p1)) ∨ ((True ∨ p2) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54036386656695609496208446927 : (((((((p1 ∧ False) ∨ False) ∧ p1) ∨ p4) → (p5 → False)) → (p3 → ((True → p4) ∨ (p1 ∨ ((False ∨ (False ∨ (p3 ∧ True))) → True))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336066998375135275923999460689 : (p1 → (((((p5 → (((((p2 ∨ p5) ∧ ((False ∧ False) ∧ p2)) ∧ False) ∧ p2) ∧ (p1 ∨ p2))) → ((p3 ∧ p3) ∨ False)) ∧ False) ∧ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323265701910104272212600712467 : (p5 ∨ ((p2 ∨ ((True → ((False → p2) → (((((p1 ∧ True) ∧ True) ∧ p2) ∨ ((p4 → (p4 ∨ p1)) ∧ p1)) ∨ p2))) ∨ False)) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671457667680808910778822117158 : ((((p2 → (((False ∨ False) ∧ (p4 ∨ ((False ∨ ((p4 ∧ p5) ∨ (p3 ∧ p5))) ∨ True))) ∨ (False ∨ (True ∧ p4)))) ∨ (p4 → (p1 → p1))) ∨ p3) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756021913918798610234265700789 : (((p1 ∧ (((p5 ∨ p5) → ((p4 → ((True ∧ ((p4 ∧ p2) → p2)) ∧ (p1 → True))) ∧ ((p4 ∨ (p1 ∨ (True ∧ p2))) ∨ True))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



