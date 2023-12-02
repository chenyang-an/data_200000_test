variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330257735818218644777799107687 : (True → (False ∨ ((p4 ∨ (p3 ∧ (p5 ∧ ((((p5 → p4) → False) → False) ∧ False)))) ∨ (True ∨ (False → (p1 → (p5 ∨ (p1 → (p2 → p1))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148156660065985194688432413231 : (((p1 → (((True → p1) ∨ p1) → ((p5 ∨ p2) ∨ ((True ∨ ((p2 ∨ p3) → False)) ∧ True)))) → (p5 → False)) ∨ (p3 ∨ (p1 → (True ∨ p3)))) := by
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
theorem thm_5_vars_353834626124354562003836796580 : (p4 → (p1 → ((((((p5 ∧ True) ∨ (p1 ∨ p2)) → ((p3 ∧ True) ∨ ((p3 → ((p1 → (False ∨ p1)) → p2)) ∨ p1))) ∨ p5) ∧ True) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258117350687618976604036188796 : ((p4 ∨ p3) → (((True → (((False ∧ p5) ∨ p3) → (p2 ∧ (p2 ∧ p5)))) ∧ (p5 → p3)) → (((p4 → (p5 ∨ p2)) ∧ True) → (p4 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h11 := h6 h10
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : ((False ∧ p5) ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190060523577321146097928837171 : ((((((p2 → p5) ∧ (p3 ∨ p3)) ∨ p1) → p4) ∧ True) ∨ (True → ((p4 ∨ ((False ∨ p2) ∨ (True → p2))) → ((False ∨ (p2 ∨ True)) ∨ p4)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48032268041822754340930666485 : (((((p4 → (p2 ∨ ((False ∧ p3) ∨ p5))) ∧ (True ∨ False)) ∧ (p4 → (((p3 ∨ False) ∧ ((p3 → False) → p4)) ∧ p4))) → (p3 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324487638462035168649986511252 : (p5 ∨ ((((p3 ∧ p1) → p5) → False) ∨ ((((p5 ∨ p2) ∧ ((p4 → ((p5 ∨ p2) ∧ p5)) ∨ False)) ∨ ((p5 ∨ p5) → p2)) ∨ (False → p1)))) := by
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
theorem thm_5_vars_54811757729968457731563739572 : (((p3 ∨ (True ∧ (p3 ∧ (p3 ∧ (True ∨ True))))) → ((((p2 ∨ p3) ∨ p3) ∨ (p5 ∧ (p3 ∧ True))) → ((p2 ∧ p1) ∨ (False → p2)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h6 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h7
          -- False on the left can always be used.
          apply False.elim h7
        case inr h8 =>
          -- Conjunctions on the left can always be decomposed.
          let h9 := h8.left
          let h10 := h8.right
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h16
            -- False on the left can always be used.
            apply False.elim h16
          case inr h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h18
            -- False on the left can always be used.
            apply False.elim h18
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h21
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- Conjunctions on the left can always be decomposed.
          let h25 := h24.left
          let h26 := h24.right
          -- Conjunctions on the left can always be decomposed.
          let h27 := h26.left
          let h28 := h26.right
          -- Disjunctions on the left can always be decomposed.
          cases h28
          case inl h29 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h30
            -- False on the left can always be used.
            apply False.elim h30
          case inr h31 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h32
            -- False on the left can always be used.
            apply False.elim h32
    case inr h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h34 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h35
        -- False on the left can always be used.
        apply False.elim h35
      case inr h36 =>
        -- Conjunctions on the left can always be decomposed.
        let h37 := h36.left
        let h38 := h36.right
        -- Conjunctions on the left can always be decomposed.
        let h39 := h38.left
        let h40 := h38.right
        -- Conjunctions on the left can always be decomposed.
        let h41 := h40.left
        let h42 := h40.right
        -- Disjunctions on the left can always be decomposed.
        cases h42
        case inl h43 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h44
          -- False on the left can always be used.
          apply False.elim h44
        case inr h45 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h46
          -- False on the left can always be used.
          apply False.elim h46
  case inr h47 =>
    -- Conjunctions on the left can always be decomposed.
    let h48 := h47.left
    let h49 := h47.right
    -- Conjunctions on the left can always be decomposed.
    let h50 := h49.left
    let h51 := h49.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h52 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h53
      -- False on the left can always be used.
      apply False.elim h53
    case inr h54 =>
      -- Conjunctions on the left can always be decomposed.
      let h55 := h54.left
      let h56 := h54.right
      -- Conjunctions on the left can always be decomposed.
      let h57 := h56.left
      let h58 := h56.right
      -- Conjunctions on the left can always be decomposed.
      let h59 := h58.left
      let h60 := h58.right
      -- Disjunctions on the left can always be decomposed.
      cases h60
      case inl h61 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h62
        -- False on the left can always be used.
        apply False.elim h62
      case inr h63 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h64
        -- False on the left can always be used.
        apply False.elim h64



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_555259079263327350520162010702 : (((p2 ∨ (True → ((p3 → ((p5 → ((((p4 → p3) ∨ p5) → (p3 ∨ p2)) ∨ False)) ∧ (((p5 ∧ (p2 ∨ p5)) ∧ False) ∨ True))) ∨ p1))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39885512511653963851302433961 : (((p2 → (((p3 ∨ p5) ∧ (p5 ∧ (True ∨ p3))) ∧ ((((p1 ∨ p4) ∨ True) → ((p3 ∧ p4) ∨ (p1 → (False → True)))) ∨ False))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177937374998324294984122064065 : ((((p1 → ((p1 → p4) → True)) → ((p4 → (p4 → True)) → p4)) ∨ p3) ∨ ((p3 ∨ (True ∨ (((p1 → (p5 ∨ True)) ∨ p4) → True))) ∨ p2)) := by
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
theorem thm_5_vars_190874743668112504421858216381 : (((((p3 → False) → p1) → (p4 ∧ p3)) → (p5 ∧ p2)) ∨ (((((False ∨ (p5 ∧ (p4 → ((p4 ∨ p3) ∧ True)))) ∨ p4) ∧ True) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317628443242788099730537933379 : (p4 ∨ ((((p3 ∧ (((p5 ∧ (((p5 ∨ True) ∧ True) ∨ True)) → ((False ∧ False) ∨ (p3 ∧ True))) ∨ p5)) → ((False ∧ True) ∧ p1)) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137799348889856893644458199524 : ((p2 ∨ (p2 ∨ (p3 → (((p5 ∧ p1) ∨ p3) → ((True ∨ ((p1 ∧ (p2 ∧ ((p3 ∧ p1) ∧ p1))) → True)) → False))))) ∨ ((False → False) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113011729951342143616513162686 : (((p5 ∧ ((((((True ∨ p5) ∧ False) ∨ p4) ∨ (((p1 ∧ p3) ∨ False) ∧ ((p2 ∨ p4) ∧ True))) → (True ∨ False)) ∨ True)) → p2) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67970310550920303951316671024 : ((p2 → (((p4 → False) ∨ p4) ∨ ((((p2 ∨ (p4 ∨ (p2 → False))) → (p3 ∧ ((p2 → (True ∧ p4)) ∨ (p4 ∧ True)))) → False) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141459919619295621891564038628 : ((((p3 → p5) → p4) ∧ (((p4 ∨ False) ∨ (False → p5)) → (((((p3 → p3) → p5) → p2) → (p2 ∨ p4)) ∧ p4))) → ((p1 ∧ p3) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 ∨ False) ∨ (False → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41614534051521527854454947922 : ((((p5 ∨ (p2 ∧ (p1 ∨ (p5 ∨ (p2 ∧ p1))))) ∨ ((((p5 ∨ p4) ∧ ((p4 ∨ ((True ∧ p1) → p5)) ∧ False)) → p5) → p4)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172856337048331637915361270256 : ((False ∧ (False ∧ (p5 → ((True ∧ ((p5 → (p2 ∨ p1)) ∨ (p4 ∧ p3))) ∨ True)))) ∨ (p5 → ((((p3 ∨ p3) ∧ p5) ∧ p3) ∨ (p4 ∨ True)))) := by
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
theorem thm_5_vars_321020510279566489983270558026 : (p4 ∨ (False ∨ ((p1 ∧ (p3 → p5)) → (((((p4 ∧ ((p2 ∨ ((True ∨ p4) ∨ p2)) → (True → (p5 → p4)))) → p3) → p4) ∨ p1) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256141305295393292742186183097 : ((True ∨ p5) → (p1 → (((p1 ∧ ((p1 → (p4 ∨ (False → ((p4 ∧ p5) ∨ p5)))) → (True ∧ ((p4 ∧ (p2 ∨ False)) ∧ p5)))) → False) ∨ True))) := by
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
theorem thm_5_vars_111722175425646501169076423719 : (((((p1 → ((False ∧ p3) → p1)) → ((((p5 ∨ p2) ∨ ((p5 → True) ∨ (p2 ∨ p3))) ∨ (p1 ∧ p4)) ∨ False)) → p1) ∨ p4) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116441861606829982031441594563 : (((p3 → (False → True)) → ((p5 ∨ (p3 → (p2 ∨ ((p3 ∨ True) → (((p1 ∨ p5) ∨ p3) ∨ p1))))) → (p3 ∨ (p3 → p4)))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4167726414260569068525875206 : (p4 ∨ ((((((p1 ∨ False) ∨ p2) ∨ p5) → p4) → (p2 → (p5 ∧ p3))) ∨ (p4 ∨ ((((False → p1) ∨ (p2 ∧ False)) ∧ False) → p3)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53239967034983236542856402650 : ((((p5 ∧ (p3 → p3)) ∨ ((p1 ∨ p5) ∧ ((False ∨ p2) ∨ p5))) ∨ ((p2 ∨ (((p3 ∧ p4) ∨ (p5 ∧ p5)) → (False → p3))) ∨ p3)) ∨ p5) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40480565055546156524686424724 : (((((p4 → p3) ∧ (((False ∨ (True ∧ (((p3 ∧ False) ∨ p1) ∧ (p4 → True)))) ∧ ((True ∧ True) ∨ (p3 ∧ True))) ∧ p1)) ∨ p2) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658143637276612561294427873701 : ((((p4 ∧ (((((p2 ∨ p2) ∧ p4) → p1) ∧ (((p3 ∧ (True → p2)) ∨ p3) → (p5 ∧ p3))) ∨ (p1 → (False ∧ p2)))) ∨ (p4 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756368898043485395179094319463 : (((p1 ∧ ((False ∨ ((p4 ∧ (((p3 ∨ p3) ∧ p1) ∧ (True ∧ ((p2 ∧ p2) ∨ ((p4 ∧ p5) → p5))))) ∧ p5)) ∧ ((p5 → p1) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198897537975535610873092678568 : ((p3 → (((p1 → (p2 ∧ p2)) ∨ True) → p4)) ∨ (p3 → ((p4 ∨ (p5 ∨ (False → p2))) ∧ (((((False ∧ p1) → p5) → p1) → p1) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∧ p1) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682853571281003895780380655926 : (((((True ∧ (p4 → p3)) → (((False ∨ (p1 ∧ p3)) ∨ ((False ∧ p4) ∨ True)) ∨ (p2 ∧ p3))) ∧ ((False ∧ True) → ((p3 → p3) ∨ p2))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617650519874276395985631435478 : ((((((p1 ∧ ((False ∧ p1) → p4)) ∨ p1) ∨ (((True ∨ (True → (p3 ∨ ((p1 ∧ ((p2 ∧ p4) ∧ p2)) ∨ p4)))) → p5) ∧ p1)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40195664156206590280640203654 : ((((((p4 ∧ p1) → p1) → ((((p1 ∧ p2) ∨ (p3 → p1)) ∨ p3) ∧ (p3 ∧ (((False → p3) ∧ p2) ∧ (False → p4))))) ∧ p4) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66163794251207700274724003843 : ((p5 ∨ ((((((p5 ∨ ((False ∨ p3) ∨ p4)) ∧ (p3 ∧ p1)) ∧ (p5 ∧ ((True ∧ p1) ∨ p3))) ∧ True) ∧ p5) ∨ (p5 ∧ (True ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678118683854057516402966731923 : (((((True ∧ ((((p4 ∨ False) ∧ (p5 → p5)) ∧ False) ∧ (p5 ∧ p5))) ∧ (True ∧ ((False ∨ p4) ∧ p3))) ∨ ((p4 → p2) ∨ (p1 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752958538321708988687652388763 : (((False ∧ (((((p3 ∨ p2) ∧ ((((p2 → (p5 ∧ p4)) ∧ (p5 → True)) → (p5 ∨ True)) ∧ p4)) → False) → ((p4 → True) → p4)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341063976060657026456129900971 : (p2 → ((p4 ∨ ((p4 ∧ (((((True ∧ True) ∨ (True ∨ ((True → p4) ∧ ((p3 ∨ (p1 ∨ True)) ∨ False)))) ∨ True) → p4) ∧ False)) ∨ True)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49733510455864616904778801021 : (((p2 ∧ ((p3 ∧ p4) ∧ (p2 → (p3 ∧ (True ∧ ((True ∨ (p3 ∨ p5)) ∧ ((p2 ∧ p4) ∨ (p1 ∨ True)))))))) → (p1 ∧ (p4 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616288444743169834570442166260 : ((((((((p5 ∨ False) → (False ∧ p5)) → (p2 ∧ p5)) ∨ (p3 → p1)) ∨ (True ∧ ((p4 ∧ (True ∨ p3)) → ((p1 → True) ∨ p5)))) ∨ False) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117529813296359208368674509592 : ((p2 ∧ ((False → ((((p1 ∨ (p5 ∨ (p5 ∨ False))) → p4) → (False ∧ p2)) ∧ ((p5 ∧ p5) ∨ (p3 ∨ (p2 ∧ True))))) → p5)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208583335033982068033295968602 : (((False → p5) → (p5 ∧ (p4 ∨ False))) → ((True → ((((True ∧ p3) ∧ (p1 ∨ True)) ∨ (p4 ∧ p2)) ∨ p4)) ∧ (p4 ∧ ((p4 ∨ p1) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (False → p5) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (False → p5) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h9
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156943552187491040740614526022 : ((((p4 → ((p5 ∧ p2) → ((p1 ∨ (p3 ∨ (p3 → False))) ∧ (p3 ∧ False)))) ∨ (False → p3)) ∨ True) ∨ (p1 ∧ (False ∧ ((p2 ∧ False) → p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114657800869724845425491342699 : ((((False → ((p3 ∨ False) ∨ (True ∧ p3))) → ((p4 ∧ (True ∨ p1)) ∨ (p5 ∨ p1))) ∨ (((p5 → True) ∨ (False ∨ p5)) ∨ True)) ∨ (True ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596520176011608297563767487961 : (((((((p3 → p1) ∧ (p2 ∧ p5)) → (True ∨ True)) → ((((p1 ∧ (p1 ∧ True)) ∧ p3) ∨ (p4 → p4)) → (True → (False ∨ False)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613560468703930494643483544363 : (((((((p2 ∧ (((((True ∨ p2) → p5) ∧ False) ∧ True) → ((p5 ∧ p1) → True))) ∨ (p3 ∨ p4)) ∨ p2) ∧ ((p5 → p5) ∧ p2)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_48941351162856906570969215384 : ((((((p1 ∨ p5) ∧ p4) ∧ (True ∨ (((p1 ∧ (True ∧ ((p2 → True) ∨ True))) → (p5 → p5)) → p2))) ∧ p3) ∨ (False ∨ (False → p3))) ∨ p5) := by
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
theorem thm_5_vars_328112322442589795947336887403 : (True → (((((True ∧ ((p3 → ((True ∧ p2) → p1)) → p3)) ∧ (p1 ∨ (p4 ∨ (False ∧ p2)))) ∧ p1) → (p4 ∧ p2)) ∨ (p5 → (p1 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116893142227235819141274678756 : (((p4 → p1) ∨ ((((p2 ∧ (((p1 ∨ ((True ∧ True) ∧ p1)) ∨ p5) ∨ p4)) ∧ ((p3 ∧ (p1 ∧ p5)) → p3)) ∨ p4) ∨ p4)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233174927118590367192831092723 : ((p5 ∧ (p2 ∨ True)) → ((p3 ∨ ((True → p2) → (p2 ∧ (p1 ∨ (((((p4 → True) ∨ p4) ∨ p3) → ((True → p3) ∧ False)) → p1))))) ∨ p3)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (((p4 → True) ∨ p4) ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h7
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- One of the premise coincides with the conclusion.
    exact h14
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : (((p4 → True) ∨ p4) ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h17
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h18 := h15 h16
    -- We need to get the right conjuct of h18 based on <expert-advice>.
    let h19 := h18.right
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611619095329404404549900859805 : (((((p2 ∨ ((((((p4 → (p2 ∧ (p2 → p4))) → p5) ∨ False) ∧ ((True ∧ p2) → ((p5 → p2) ∧ p1))) → p1) ∧ p5)) → p2) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341346022593237423738827154520 : (p2 → ((((p4 → ((True ∨ p4) ∨ True)) → False) ∧ (p3 ∧ (((p5 ∨ ((True → p4) ∨ (p1 → p1))) ∧ (p5 → p3)) ∨ (False → p2)))) → p5)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h13 : (p4 → ((True ∨ p4) ∨ True)) := by
          -- Implications on the right can always be decomposed.
          intro h14
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h15 := h3 h13
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h17 : (p4 → ((True ∨ p4) ∨ True)) := by
          -- Implications on the right can always be decomposed.
          intro h18
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h19 := h3 h17
        -- False on the left can always be used.
        apply False.elim h19
  case inr h20 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h21 : (p4 → ((True ∨ p4) ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h22
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h23 := h3 h21
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27718827075553848757013468124 : (((p2 ∨ p4) → (p5 ∨ ((((False ∧ ((True ∧ ((p3 ∨ (p2 ∨ False)) ∧ p2)) ∨ p2)) → True) → (p4 ∧ ((False → p5) → p1))) ∨ True))) ∧ True) := by
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
theorem thm_5_vars_16573570329625076901863846711 : (((((((p1 ∧ False) → p4) → (((True ∨ False) ∧ (p5 ∧ p4)) ∨ p4)) ∨ (p4 ∨ ((p3 ∧ p2) ∨ True))) ∧ p3) ∨ (p2 → (p2 ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148016159252973966418110536764 : ((((p4 ∧ (p4 ∨ ((False ∧ (True → (p1 ∧ False))) ∧ False))) ∧ ((False → (p5 → p3)) ∧ False)) ∨ (p5 ∧ p5)) ∨ ((p4 ∨ (p2 → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590106906666985555653555925700 : ((((((((p5 ∧ p3) → True) ∧ ((p2 → (p2 → True)) ∨ False)) ∨ (p1 ∨ (True ∨ ((False ∧ (True → (p1 ∨ p2))) ∧ p1)))) → p3) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43411206670065371579143741137 : (((((p1 ∧ ((True ∨ p5) ∨ ((p4 → p5) → (p1 ∧ p5)))) ∨ (p5 ∨ ((p2 → (p3 → p3)) → (p1 ∧ (p1 ∨ p5))))) ∨ p4) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219434352941925438599459071514 : ((p4 ∨ ((True → True) ∨ p5)) → ((p4 ∨ ((p4 → ((False → p4) ∧ p4)) ∧ p2)) → ((p1 ∧ ((False → p4) ∧ p5)) ∨ (False → (p5 ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h5
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h8
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h10
        -- False on the left can always be used.
        apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h15
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
        -- False on the left can always be used.
        apply False.elim h18
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h20
        -- False on the left can always be used.
        apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66590273476466328748271250510 : ((True → (((((p1 ∨ ((True ∨ ((p3 → p3) ∨ (p4 ∨ (p3 ∧ p4)))) ∨ p5)) → p3) → (p2 → p1)) → p1) ∨ ((True ∨ p2) → True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125533546429134370775651635172 : (((True → False) ∧ (True → ((((p2 ∧ p5) → True) ∨ p4) ∧ (((((p1 ∨ p4) → ((p1 ∨ p3) → p2)) → p4) → p4) ∧ False)))) → (p3 ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134418839736742786287267667850 : (((p3 → ((p5 → ((((p3 → (p2 ∨ p4)) ∨ p4) ∧ ((p2 → (p4 ∨ (p3 ∨ p2))) ∨ p5)) ∨ p5)) → p2)) ∨ p5) ∨ ((p3 ∧ p2) → p2)) := by
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
theorem thm_5_vars_219219998760851830421769412666 : ((p1 ∨ ((p3 ∧ p3) ∧ p5)) → ((p1 ∨ ((p2 → ((False ∨ (p2 ∧ False)) → p3)) ∨ (p1 ∨ (p5 ∧ p2)))) → ((p1 → (p5 ∧ p5)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Conjunctions on the left can always be decomposed.
        let h16 := h14.left
        let h17 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h21.left
          let h23 := h21.right
          -- Conjunctions on the left can always be decomposed.
          let h24 := h22.left
          let h25 := h22.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h29 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h30 =>
          -- Conjunctions on the left can always be decomposed.
          let h31 := h30.left
          let h32 := h30.right
          -- Conjunctions on the left can always be decomposed.
          let h33 := h31.left
          let h34 := h31.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135393217767392310634514152181 : (((((p3 → p3) → ((p4 → (True ∨ (p1 ∧ ((p2 ∨ p4) ∧ True)))) ∧ p5)) → (p4 ∨ p3)) ∨ (p2 ∨ (False ∧ p3))) ∨ ((p2 → True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245365154292854821518553235443 : ((p2 ∧ p3) ∨ ((False ∧ ((((True ∧ False) ∧ (p5 ∨ (False → p2))) ∨ p3) ∧ p2)) ∨ (True ∨ (((False ∧ (False → p1)) ∧ (p5 ∨ p1)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200480937095168291697721644417 : (((False ∧ True) → (p5 ∧ (True ∧ (p1 → True)))) → (((((True → p2) ∨ True) ∨ (((((True ∧ p4) ∨ p4) ∧ False) → p2) ∨ p3)) ∨ p2) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705658254009301952771044247104 : (((((((True → p2) ∧ p2) → p2) ∧ (p1 ∧ p3)) ∧ ((p2 ∨ (p5 ∧ (((((p4 ∨ (False → p3)) ∧ p4) ∨ p1) ∧ p5) → True))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58932090901241182747101775427 : (((p1 ∧ p3) ∨ (True ∧ (((((p5 → p3) ∨ True) ∧ (True ∧ (p4 ∨ False))) ∨ (p3 ∨ True)) ∨ (p4 → (p5 → ((True ∨ p2) ∨ p3)))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2568711402487784571639026993 : ((True → (p4 ∨ ((True ∨ True) → (p3 ∧ True)))) ∨ ((p4 ∨ (False → p5)) ∧ (((False ∧ False) → p5) → ((p3 → p3) ∧ (True ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309467825879868052711475108434 : (p2 ∨ (((((p4 ∧ ((p4 ∨ p3) ∧ p5)) ∧ True) ∨ (True ∨ (False ∨ (p3 ∧ p4)))) → (False ∧ (((p3 ∧ p4) ∧ p1) → p2))) → (p5 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p4 ∧ ((p4 ∨ p3) ∧ p5)) ∧ True) ∨ (True ∨ (False ∨ (p3 ∧ p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136641528404331642836936710800 : ((((p3 ∧ p5) → p4) → (((p2 ∨ ((p2 ∨ True) → True)) → (False ∧ p5)) → (((p5 ∨ (p4 ∧ p5)) ∧ p2) ∨ p2))) ∨ ((p5 → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60358741547049211676161703462 : (((p2 → p5) → (((p1 ∧ (((p4 ∧ p2) ∧ (False → p3)) → (p1 ∧ (p5 ∧ p3)))) ∧ p3) ∧ ((p1 → (p2 ∨ (p3 ∧ True))) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188556946801811261088575975143 : ((((((p3 ∨ p3) → p2) → p2) ∨ True) ∧ (p4 → p4)) ∧ (((((p3 → (p2 ∧ False)) → (p5 ∧ (True ∨ True))) → (p4 ∨ p2)) ∨ p5) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704299682602483850338713193433 : (((((p4 → ((p3 ∧ p4) ∨ True)) ∧ (p1 ∧ (True ∨ False))) → ((((((p3 → p4) ∨ p5) → p5) ∧ p2) ∨ True) ∨ (p5 ∧ (p4 ∧ p2)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171933915443978189368545308008 : ((((p5 ∧ (p2 → ((False ∧ p3) ∧ (p5 → (p3 ∧ p1))))) ∨ p5) ∧ (False ∧ p5)) ∨ ((False ∧ p3) → (((p5 ∨ False) → p4) ∧ (p2 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20517028180532313655671903737 : (((True ∨ ((((True → p5) → (False → (p4 ∧ True))) ∨ p5) ∧ (p3 → p3))) → ((True ∧ (p2 ∧ p2)) → (((p4 ∨ p1) ∨ p2) ∨ p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618942985773938064981420869848 : ((((((p4 ∧ p5) ∧ p1) ∨ (((p2 ∧ (((p1 ∨ p3) ∨ (True ∧ True)) → (p2 ∨ ((p3 ∧ (p2 → p5)) ∨ p5)))) → p4) ∨ p5)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_258714685403825642780358997700 : ((True → True) → ((((((True ∧ ((p5 ∨ (p3 ∨ p1)) ∨ p2)) → False) → p2) → ((p1 ∨ True) ∧ ((p1 ∧ p4) ∨ False))) → False) ∨ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247438022881660768955948902439 : ((False ∨ p2) ∨ ((p2 ∧ (p3 ∧ p1)) ∨ (True ∨ (p2 ∨ ((p1 ∨ p2) ∨ (p4 ∨ (True → (p2 ∨ ((p5 → p1) → (p3 ∧ (True → p1))))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355432350747542994283064599686 : (p5 → ((((((((p5 → (((True → p1) ∨ p2) ∧ False)) ∨ p4) ∧ (p1 ∧ p3)) ∨ (p4 ∨ True)) ∨ (p5 ∨ p4)) → False) → False) ∧ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((((p5 → (((True → p1) ∨ p2) ∧ False)) ∨ p4) ∧ (p1 ∧ p3)) ∨ (p4 ∨ True)) ∨ (p5 ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137533247954514449925874217735 : ((p5 ∧ (p1 ∨ ((True → ((((p3 ∨ (False → p1)) ∨ False) → (((p2 → (p2 → p2)) ∧ False) ∧ p3)) ∨ p5)) ∨ False))) ∨ ((False ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604941052383404727884405280440 : ((((p1 → (False ∧ ((p3 ∨ (False ∧ (p4 ∧ ((((p1 ∧ ((p4 → p2) ∨ p5)) → False) → False) ∧ True)))) ∨ (False ∨ (p2 → True))))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690337683344634268445997043381 : ((((p3 → ((p2 ∧ (((((True ∧ p5) → True) ∨ (False ∧ False)) ∨ p1) ∧ p3)) → False)) ∨ ((p1 ∧ ((p5 ∨ False) ∧ p4)) ∨ (p4 ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49726369580897685575009476863 : (((p1 ∧ (((p4 → p2) → ((True → (p1 → True)) ∨ p2)) ∧ ((p3 ∧ p3) ∨ ((True → p5) ∧ (p1 ∧ p1))))) → (p2 → (p2 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133717506863913885415028811749 : (((((p1 → (False ∧ (((p3 ∨ p1) → p4) ∨ p3))) → (False ∧ p2)) ∧ (p2 → (p4 → (p3 ∧ (p5 → p5))))) ∧ p2) ∨ ((p2 ∧ p1) → p1)) := by
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
theorem thm_5_vars_60344484004882928706721798016 : (((p2 → p2) → (p5 ∨ ((False ∧ p1) ∨ ((p5 ∨ ((False → (p5 ∧ p1)) → (((p4 → (p3 → (p1 ∨ p5))) → False) ∨ False))) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_97054677345414105239307823356 : ((p1 ∨ (True → (((((True ∨ ((True → p5) ∧ p5)) ∨ (p4 → p5)) ∧ True) ∧ ((p3 ∧ p1) ∧ ((p5 ∨ p1) ∧ p2))) ∧ (True → p3)))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191451450398956349309499258679 : (((p1 → p5) → ((True ∧ (p2 ∧ (p2 → p2))) ∨ False)) ∨ ((p1 → True) ∨ ((((((p4 ∧ p1) → (False ∨ True)) ∧ p1) → p1) → p3) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114377738951088507033350816040 : ((((((p4 → ((p4 → p5) ∨ ((False ∨ True) ∧ p2))) → False) → (p4 → (p2 ∨ False))) → p2) ∨ ((p4 ∨ (p3 → p1)) → True)) ∨ (True ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585353650416025293795972783209 : ((((((((False ∨ (((p4 → (p4 ∨ p4)) ∧ False) ∨ ((p5 ∧ (p4 ∧ p5)) → p5))) ∨ False) ∨ (p4 ∨ (p5 ∨ p4))) ∧ p2) ∧ p4) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655299856514846891891481997877 : (((((p3 ∧ ((((p3 ∨ (p5 ∨ True)) → ((True ∨ ((True ∧ p3) → p2)) ∧ (p4 ∧ p1))) ∨ True) → p2)) ∧ (False → True)) ∨ (p3 ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_219740666512460560445345522450 : ((p1 → (p2 → (p4 ∧ p2))) → ((True ∧ (((False → p2) ∧ (p1 → ((False → True) ∧ False))) ∧ (((True → False) ∨ False) ∧ p4))) → (p4 ∨ False))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h9 := h6.left
  let h10 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197718560521207491260572267971 : ((((True → False) ∧ False) ∧ ((p2 ∨ True) ∧ p1)) ∨ (p4 → (p5 ∨ (p4 ∧ ((True → (p4 ∧ p5)) → (p5 ∨ (True → ((False ∧ p5) → p3)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709025462493657219715683267970 : ((((((False → p4) ∨ True) ∧ (p4 ∧ (True ∨ False))) → ((((p5 → p3) ∨ ((p5 ∨ p5) ∨ ((False ∧ True) ∧ True))) ∨ False) ∨ (p5 ∨ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118616471905808503487861501000 : ((p4 ∨ (((p3 ∨ ((p1 ∧ ((p2 ∧ p1) → p3)) → p5)) → (p5 ∧ p5)) ∨ (p3 → (p2 → (True → ((True → True) ∨ p5)))))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49203205208148103507360392199 : ((((p5 → (False ∧ p3)) ∨ ((False → p4) → (((p3 → ((p4 → True) → ((p4 ∧ p4) ∧ False))) ∧ p1) ∨ True))) ∨ ((p5 → p2) ∧ False)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303137473785530714317462740018 : (False ∨ (p3 → ((p4 → p3) ∧ (((p5 ∧ (p5 → (p2 ∧ p1))) → ((p1 ∧ (True ∧ p2)) ∧ (p2 ∧ False))) → (p1 ∨ ((p4 ∧ p3) → p4)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53777208520403523118791421194 : (((((False ∧ (False ∧ True)) ∨ (p2 ∨ (p5 ∨ p1))) ∨ p5) ∨ (p5 ∨ (((p3 ∧ p3) ∨ p1) → ((p2 ∨ ((p5 ∨ False) → True)) ∨ p5)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241481097378978011668906264745 : ((False → p2) ∧ ((p5 ∧ (((p1 → (False → p1)) ∨ True) → p5)) ∨ ((((False → (p2 → p5)) → ((True → False) ∧ p5)) ∧ (p1 ∨ False)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200687583092421686495808396788 : ((p2 ∧ (((p2 ∧ (p5 ∨ p4)) → p3) ∨ p2)) → ((((p2 ∨ p5) ∧ True) → ((p3 → True) ∧ (p1 → ((p1 → p4) → (p1 ∧ p4))))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h1.left
    let h15 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  -- Conjunctions on the left can always be decomposed.
  let h18 := h2.left
  let h19 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h1.left
    let h22 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h24 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h25 := h5 h24
      -- One of the premise coincides with the conclusion.
      exact h25
    case inr h26 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h27 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h28 := h5 h27
      -- One of the premise coincides with the conclusion.
      exact h28
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h1.left
    let h31 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h31
    case inl h32 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h33 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h34 := h5 h33
      -- One of the premise coincides with the conclusion.
      exact h34
    case inr h35 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h36 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h37 := h5 h36
      -- One of the premise coincides with the conclusion.
      exact h37
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317882341124130546888507343709 : (p4 ∨ ((True ∧ ((p4 → ((((p2 → False) ∧ ((p3 → (((p5 ∨ p1) ∧ p1) ∧ p2)) → False)) ∨ (p2 ∨ p1)) ∧ True)) → (p1 ∧ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670466197231998377144873846215 : (((((p5 ∧ p5) ∧ ((False ∨ (p3 ∧ ((True ∧ False) ∨ (True ∧ (((p4 → p3) → p5) ∨ p1))))) ∨ (p1 ∨ True))) ∨ ((True ∨ p3) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337780052764012520229988679865 : (p1 → ((False ∨ (p5 ∨ ((p3 ∨ (((p1 ∨ p5) ∨ p3) ∧ (p2 ∧ p3))) ∨ (p3 → p5)))) ∨ ((p1 ∧ p1) → (True ∨ ((False ∧ p5) ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



