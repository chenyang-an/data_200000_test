variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310833024192374497357837455393 : (p2 ∨ (((p5 ∧ p4) ∧ p4) → ((((p1 ∨ p4) ∧ True) → False) → (False ∧ (True ∧ ((((p2 ∨ (p5 → (p1 → p4))) → p1) ∧ True) ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : ((p1 ∨ p4) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h9
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h15 : ((p1 ∨ p4) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h16 := h2 h15
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h1.left
    let h19 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h22 : ((p1 ∨ p4) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h23 := h2 h22
    -- False on the left can always be used.
    apply False.elim h23
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184295132902085652604767360545 : (((((p2 ∨ p1) → True) ∧ (p3 → ((p5 → p5) ∧ p2))) → p1) ∨ (p3 → ((False ∧ ((False ∧ False) ∧ ((False ∧ (True ∨ False)) ∧ False))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351827665204919455007714674932 : (p4 → ((p1 ∧ ((False → (((False ∧ True) ∨ p1) → (p4 → p3))) → False)) ∨ (((p1 → p3) → ((p1 ∧ (p1 → p1)) ∧ p5)) ∨ (p1 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182904251413166252671693941523 : ((((p3 ∨ p2) ∨ p3) → ((p1 ∧ ((p4 ∧ p2) → p1)) → True)) ∧ ((((p5 ∧ p5) ∨ p4) → False) ∨ ((((True → p1) ∧ p4) ∨ p5) ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749961757682843308695831649659 : (((True ∧ (((((p5 → False) ∧ (True → (p4 ∨ (p2 → ((False → False) ∧ (p2 ∨ p1)))))) ∨ ((p1 → p5) → p5)) ∨ (p4 ∧ p4)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157668233834851407365275705286 : ((((p5 → (False → ((p2 → (False ∨ p5)) ∧ p4))) → ((p1 ∧ p2) → p3)) ∨ ((False ∧ p4) ∨ False)) ∨ ((p4 → p5) ∨ ((False → p1) ∨ p4))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50970891993500679775402895263 : (((((p2 ∨ (p4 ∨ p2)) → False) → ((p5 → ((((p5 → False) ∨ p2) ∨ False) ∨ p1)) → p3)) ∧ (p1 ∨ (((p5 ∧ p5) → p5) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731382342054963650516700585945 : ((((p5 ∨ (p1 ∨ p2)) → (((((p4 → (p4 → (True ∨ p5))) ∨ (True ∧ (p5 ∨ (p1 → p1)))) ∨ ((False ∨ False) → False)) → p1) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114777874367194913589056075516 : (((((p5 ∧ ((p1 ∧ (True ∧ ((False → True) ∧ p1))) ∨ True)) ∨ True) ∨ p3) ∧ ((p3 ∨ (False ∨ p3)) → ((p3 → False) → False))) ∨ (p4 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h9
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114074166543968576301392082538 : ((((((p2 ∧ True) → p4) ∨ p2) ∨ ((p2 ∧ (p2 ∧ (p1 → (p3 ∨ ((False ∨ p1) ∨ True))))) ∨ True)) ∨ ((True ∨ True) → False)) ∨ (p3 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303167289343363597243457266738 : (False ∨ (p4 → ((True ∧ ((p1 → (False ∧ ((p5 ∨ (((p5 ∧ False) ∨ (p4 ∨ True)) → ((p1 ∨ True) → p4))) ∨ p5))) ∧ (p2 ∧ False))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248186028100163266665974094774 : ((p2 ∨ False) ∨ (p1 → ((((p1 → False) ∨ ((True → False) → (True → True))) ∨ p2) → ((True ∨ (False → True)) → (p3 ∨ (True ∨ (p4 ∧ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_951158874719420150535637976958 : ((((p1 ∨ (p4 → p1)) ∧ ((((((p1 ∧ p1) ∨ True) → False) ∨ p4) ∨ ((p5 ∧ (p5 ∧ (p4 ∧ p5))) ∧ False)) ∧ ((p5 → p2) ∨ p3))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h9 =>
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h10 =>
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h12 =>
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h13 =>
          -- One of the premise coincides with the conclusion.
          exact h4
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- False on the left can always be used.
      apply False.elim h16
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h3.left
    let h25 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h28 =>
          -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
          have h29 : ((p1 ∧ p1) ∨ True) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h27, we can now drive its conclusion.
          let h30 := h27 h29
          -- False on the left can always be used.
          apply False.elim h30
        case inr h31 =>
          -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
          have h32 : ((p1 ∧ p1) ∨ True) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h27, we can now drive its conclusion.
          let h33 := h27 h32
          -- False on the left can always be used.
          apply False.elim h33
      case inr h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h35 =>
          -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
          have h36 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h34
          -- We have shown the premise of h23, we can now drive its conclusion.
          let h37 := h23 h36
          -- One of the premise coincides with the conclusion.
          exact h37
        case inr h38 =>
          -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
          have h39 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h34
          -- We have shown the premise of h23, we can now drive its conclusion.
          let h40 := h23 h39
          -- One of the premise coincides with the conclusion.
          exact h40
    case inr h41 =>
      -- Conjunctions on the left can always be decomposed.
      let h42 := h41.left
      let h43 := h41.right
      -- Conjunctions on the left can always be decomposed.
      let h44 := h42.left
      let h45 := h42.right
      -- Conjunctions on the left can always be decomposed.
      let h46 := h45.left
      let h47 := h45.right
      -- Conjunctions on the left can always be decomposed.
      let h48 := h47.left
      let h49 := h47.right
      -- False on the left can always be used.
      apply False.elim h43
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56471599913395760635675936256 : ((((p4 ∨ False) → (False → True)) → ((((p2 → p5) ∨ ((((p3 ∨ p4) → p4) ∧ p4) ∧ (p1 ∧ (p1 ∧ p4)))) ∨ (p2 ∧ False)) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336116619259222988377294406697 : (p1 → ((((True ∧ (((p4 ∧ (p2 → p5)) → ((p2 → p5) ∧ ((True → False) → ((p2 ∨ True) → False)))) ∨ False)) ∧ (p3 → p2)) ∨ p5) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134068383073797982455955428899 : ((((((((((True ∧ True) → ((p2 → ((p5 ∨ p4) ∨ True)) → True)) → True) ∨ p2) ∧ p2) ∧ False) → p3) → False) ∨ p3) ∨ (p4 ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708170085561194512364447020031 : ((((p1 → ((p3 ∧ (False ∧ (False → False))) ∨ p4)) ∨ ((((((p2 ∨ False) → (True ∧ ((True → True) ∨ p2))) → p4) ∨ True) ∧ True) ∨ p5)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_137229521809200210284454931684 : ((p1 ∧ (((True ∧ p1) ∧ (((p4 ∨ (((p5 ∨ (p5 ∨ (True ∨ (p4 → False)))) ∨ p3) ∨ p3)) ∧ p3) ∨ p3)) → p4)) ∨ (p1 ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133578857332461534072191254294 : (((((True ∨ (True → (p3 → False))) → ((p1 ∧ (((p2 ∨ (p1 ∨ True)) ∧ p3) ∨ p1)) ∧ (p1 ∨ False))) ∨ True) ∧ True) ∨ (p5 ∧ (p3 ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40674028908222173498113234015 : (((((((p1 ∧ (p4 ∨ p2)) ∧ p3) → (False → (((p2 → (p4 ∧ (p3 → p4))) ∨ p1) ∧ p5))) ∧ ((p1 → p1) ∧ True)) → p2) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78694560420397633830929616551 : ((((p3 ∨ ((p4 → ((p4 ∨ (False ∧ True)) ∨ ((p3 ∨ (False ∨ True)) ∧ p5))) ∨ True)) → ((True ∧ p5) ∧ (False ∨ p3))) ∧ (p3 → p5)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p3 ∨ ((p4 → ((p4 ∨ (False ∧ True)) ∨ ((p3 ∨ (False ∨ True)) ∧ p5))) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774511695449768140176930455908 : (((False ∨ (((p4 ∨ ((p1 ∧ (p2 ∨ ((True ∨ (False → False)) ∧ True))) ∧ p5)) ∧ p3) ∨ ((p4 ∨ p5) ∨ (p2 ∨ (p5 ∨ (p3 ∨ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354752327334998011226006470355 : (p5 → (((((((((p3 → (p1 ∨ True)) → p2) ∨ p5) ∧ True) ∨ p4) ∧ True) → p4) ∧ (p5 ∧ (((p1 ∧ False) ∨ (False ∧ p5)) ∧ True))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118577518432511067115190060987 : ((p4 ∨ ((((p5 → (p3 → p5)) ∨ p4) ∧ ((p5 ∧ ((p1 ∧ (p1 → (p5 ∨ p1))) ∨ (False ∧ (True → False)))) ∧ p4)) ∨ p4)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352140351390454330769824569911 : (p4 → (((p5 → ((p2 ∧ p1) ∨ False)) → p2) → ((((p1 → (True ∧ (p1 → ((p5 ∧ p5) ∧ p2)))) ∨ p4) → p3) ∨ ((True ∨ False) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53525118369332641012629779474 : (((p3 → (((((p1 ∨ p5) → p5) ∨ (False ∨ p4)) ∨ False) ∨ p3)) → (p1 ∧ (False ∧ ((p5 → p5) ∧ (((p4 → p3) → p3) ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323222996122141129628190989196 : (p5 ∨ (((p3 ∧ ((p1 ∧ (p2 → ((p1 ∧ p2) → True))) ∧ p3)) ∧ (False ∧ (False → ((False ∧ (p5 → p3)) → (p2 ∧ p4))))) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193418187674354872605316712060 : (((p2 ∨ False) ∧ ((True → (p5 → p3)) → (p4 ∨ p2))) → (((p2 ∨ p4) → (p1 ∧ ((p5 ∨ False) → (p3 → ((p4 ∨ p5) → p4))))) → p1)) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (p2 ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134091743340998277658542407800 : ((((True ∧ (p4 ∨ (((p2 ∨ p2) ∨ (True ∨ p1)) ∧ ((p4 ∨ p5) ∧ (True → ((p5 → p1) → p1)))))) → p4) ∨ p1) ∨ (True ∨ (p4 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257956798754554160583376818841 : ((p4 ∨ False) → (False ∨ (((p2 ∨ p3) ∧ (((p3 ∧ True) → (p2 ∨ (((True ∨ p4) ∨ p4) → p5))) ∨ ((p5 → True) → (p3 → p5)))) ∨ True))) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799050058507706695649360346498 : (((p1 → ((p3 ∨ p3) → (((p5 → (p2 ∧ ((p3 → (((p1 ∨ False) → (True ∨ ((True → p3) → True))) ∨ True)) ∧ p2))) → p4) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67664919646047859903583279362 : ((p1 → (p5 ∨ ((((p5 ∧ True) → p5) ∧ (p2 ∧ False)) ∨ ((True ∧ ((p1 ∧ (((p5 ∨ False) ∧ p3) ∨ True)) ∨ p5)) ∨ (p3 → p5))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232347693845787448806261238228 : (((p4 → p1) → p5) → (((p5 ∨ p5) → (p5 → ((p2 → (p5 → ((True ∨ (p4 ∧ p3)) → False))) ∨ (p3 ∨ p5)))) ∨ ((p5 ∨ p1) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303905914363676192983384397050 : (p1 ∨ ((((((p4 ∧ ((p3 ∨ True) ∧ p5)) → p3) ∨ p2) → ((p5 → False) ∧ True)) → ((p2 ∧ (p2 ∨ (p4 ∧ (p1 → p4)))) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123734305887677850744170268176 : (((((False → p5) ∨ False) ∧ ((((p1 ∧ p2) → False) ∨ (p3 ∧ p3)) ∧ p5)) ∧ (p4 ∨ ((p3 → p2) ∨ ((p3 → p5) → False)))) → (p2 ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h21 =>
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59055266193635478403617833293 : (((p4 ∧ p4) ∨ (((p2 ∧ p3) → p1) → (p5 ∧ (p3 → (((p5 ∧ p4) → (p2 ∧ False)) → (p2 ∧ (((p1 ∧ False) → False) ∧ p4))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329695510388158025738005764590 : (True → ((p4 ∨ p4) → (((p1 ∨ (p5 ∨ (((p1 → (p1 ∨ ((p5 ∨ p3) → p2))) ∧ ((p2 → (True ∧ True)) ∧ p5)) ∨ p2))) ∨ p4) ∨ p1))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106998077102591635301875832947 : ((((p4 → p4) → (p3 ∨ False)) ∨ (True → (((p3 → p4) → ((((p3 ∧ p4) ∨ (False ∧ p2)) ∨ p1) ∨ (True ∨ p3))) ∧ True))) ∧ (p4 → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184106465844700426478401574126 : ((((True ∧ p3) ∨ ((p5 → (p1 → p4)) ∨ (p2 ∧ p2))) ∨ False) ∨ ((False ∨ (((((p3 → p3) ∨ p2) → True) ∨ True) → False)) → (False ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((((p3 → p3) ∨ p2) → True) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : ((((p3 → p3) ∨ p2) → True) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777074769611716282413462601993 : (((p1 ∨ ((p2 ∨ ((p5 → (((p2 ∨ p4) → (False ∧ (p3 ∧ ((p4 ∧ p3) ∨ (True ∧ (p3 ∧ p5)))))) → False)) ∧ True)) ∨ (p4 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178347005722520488911235988977 : (((p1 ∧ (((((p1 ∧ p3) → p3) ∧ False) ∧ False) → p1)) ∨ (p5 ∨ p1)) ∨ (p3 ∨ (((p3 ∨ (p4 → False)) ∨ True) ∨ (p1 ∧ (p2 ∧ p5))))) := by
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
theorem thm_5_vars_783288726949354856108580649955 : (((p3 ∨ ((((p4 ∨ p1) ∨ (p1 ∧ (((p2 ∧ True) → (p5 ∧ p5)) ∧ p4))) ∧ ((p1 ∨ p3) → p1)) ∨ ((p4 ∧ p4) ∨ (p2 ∨ True)))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152623546148442130754899005834 : (((p1 ∨ False) ∧ (((p5 ∨ (True ∧ p5)) → (p4 ∨ (p5 → (p5 ∧ (True → ((p2 → p2) ∧ p1)))))) ∧ p4)) → (((p5 → p2) ∨ p5) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61078416375959221427013069748 : ((False ∧ ((p4 ∧ (((p4 → ((p2 → p2) → (True ∨ ((p1 ∨ (False ∧ True)) → p3)))) → p1) → p5)) ∧ (((p1 ∨ p5) → True) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797266212411215276667342192256 : (((p1 → (((((p1 ∨ (p1 ∨ (True ∨ True))) ∧ (((p3 ∧ p2) ∧ p4) ∨ ((p1 → (True ∧ (p3 → p5))) → p5))) ∨ p3) → False) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_140620219818966716306075626325 : ((((p5 ∧ False) → (False ∧ (p2 ∧ (((p4 ∧ ((p1 → False) → p5)) ∧ True) ∨ p5)))) → (p2 ∨ (p1 ∧ (p4 ∧ p3)))) → ((p5 → p4) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ False) → (False ∧ (p2 ∧ (((p4 ∧ ((p1 → False) → p5)) ∧ True) ∨ p5)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- False on the left can always be used.
    apply False.elim h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h17
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41983092734444416793351351364 : ((((p3 ∨ p5) ∧ ((p4 → (False ∨ (((p1 ∨ (((p5 → p2) → p3) ∨ True)) → p5) → (((False → p2) ∧ p4) → p4)))) → p4)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587664224394683006982589127131 : ((((((((p2 → ((p5 ∧ p1) ∧ (p5 ∨ p4))) → p5) ∧ ((p1 ∧ ((p4 ∧ p2) ∧ p3)) ∧ (False → (p2 → p3)))) → p1) ∨ p1) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257393453114348170254542879601 : ((p2 ∨ p5) → (((p2 ∧ (False ∧ (False ∧ p1))) ∨ True) ∨ (((((False ∧ p1) ∧ True) ∧ (p4 ∧ p2)) → (p5 ∨ (p4 → (p4 ∧ True)))) ∧ True))) := by
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
theorem thm_5_vars_613155188651528960711545916596 : (((((((p2 ∨ (((p3 → (True ∨ (False ∨ p3))) → p1) ∧ p1)) ∨ ((p5 → True) ∧ (p2 ∧ False))) ∨ (p5 → p5)) → (p2 ∧ p4)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_711128142595956903155931180252 : ((((p1 ∧ ((p4 ∧ (False ∨ p5)) ∨ True)) ∧ (p3 ∨ (((((((p5 ∧ p5) ∨ (p2 ∧ p4)) ∧ p3) → (p3 ∨ True)) → p1) ∨ p5) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157149757627056994839930854691 : (((((((p2 → (True ∨ (p1 ∨ p5))) ∨ (p3 → p5)) → p4) ∧ ((p3 ∨ True) ∨ p3)) ∨ False) → False) ∨ (((True → (p2 ∨ p1)) ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323802871907719418829847531525 : (p5 ∨ (((p4 ∨ p2) → ((((p2 ∧ p3) ∨ (p3 ∨ False)) ∨ ((False ∧ p2) ∨ True)) ∨ (p3 → p4))) ∨ (p3 → ((p4 ∧ False) ∧ (p5 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257791521628374370633625143599 : ((p3 ∨ p5) → (((p1 ∨ ((p4 ∧ p3) ∨ (p5 ∧ ((p1 ∧ p2) ∧ (((p2 → (True → p5)) → ((p1 ∨ p2) → False)) ∧ p3))))) ∨ True) ∨ True)) := by
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
theorem thm_5_vars_27325207522791449403051387846 : (((True ∧ p4) → (p5 ∨ (((p1 ∨ (p1 ∨ (((p2 ∧ (p1 → p1)) ∧ (False ∧ True)) → (((True ∨ p2) → False) ∧ p3)))) → p2) ∨ p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_927819246859632439377447156614 : ((((((p5 → ((p1 ∨ False) ∧ True)) → False) → (p3 ∧ p1)) ∧ ((True ∨ ((p2 → p4) ∨ (p4 ∧ p5))) → (p1 ∧ ((p3 ∧ p4) ∧ False)))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ ((p2 → p4) ∨ (p4 ∧ p5))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178202189404427029615552663170 : (((False ∨ (p4 ∧ (((p3 → ((p3 → p1) ∨ p2)) ∧ p5) ∨ True))) → p2) ∨ ((False ∧ p2) ∨ (True ∨ ((((False ∧ p4) → p5) ∨ p1) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317845744611956678419030410815 : (p4 ∨ (((p2 ∨ (p1 → False)) → (((((False ∧ (p4 ∧ p2)) ∧ p3) ∨ p5) ∨ (p1 → ((p4 → p5) → p2))) ∨ (p4 ∨ (p1 → True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615230514435028467812127191586 : (((((p4 ∧ (False ∨ ((p2 ∨ p1) ∨ (((True → (p1 → p3)) ∨ p3) → (p5 → p2))))) ∧ ((p1 ∧ (p5 → (p4 ∧ p3))) ∨ p1)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_184428603141091927180372581212 : (((((p3 ∧ p1) ∨ p4) ∧ ((p5 ∧ p3) ∨ p2)) ∧ (p1 ∨ p3)) ∨ ((p2 → ((p2 → (True ∧ (p4 → p4))) → ((p2 → p1) ∨ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38054444000295831977783888435 : (((((p5 ∧ (p4 ∧ ((((p5 ∨ (((p2 ∨ p1) ∨ False) → p1)) ∧ p1) ∧ (p2 → True)) ∨ p2))) → (p1 → False)) → (p2 → p4)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205935808404329936864444210292 : ((False ∧ ((p3 → p4) ∧ (p2 → p4))) ∨ (((p3 ∨ p1) ∨ p1) ∨ (((p4 ∨ (((((p4 ∧ p2) ∨ True) ∧ p4) ∨ p2) ∧ False)) ∧ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659057056197268447083125799038 : ((((p2 → (((((True ∨ p4) ∧ ((p4 → ((p1 → p1) → p1)) ∨ p3)) → (p4 ∧ p2)) → ((p3 → p1) ∨ p2)) → p5)) ∨ (False → p4)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_59568113438427549754849559696 : (((p3 → p4) ∨ (False ∨ (((p4 → False) ∨ True) ∧ ((p1 ∧ ((p5 ∧ p3) → p2)) ∨ ((p2 ∧ (p1 ∨ p2)) → (p1 → (p3 ∨ True))))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115722391668159050585582546173 : (((((p2 ∨ p1) ∧ (p2 ∨ p5)) → p4) → (((p1 ∧ ((p1 ∨ p2) → (p4 ∨ p1))) ∧ (((True → p4) ∧ p2) → True)) → p4)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134241417907312736906306030142 : ((((((p1 → p3) ∧ False) ∨ p3) → (((((p2 → ((p5 ∧ p3) ∧ (p1 ∧ p5))) ∧ p1) → p4) → p5) ∨ False)) ∨ True) ∨ (p2 ∨ (p1 → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65915284567152053065121724019 : ((p4 ∨ (p3 ∧ (p4 ∧ (p2 ∨ ((((((p4 ∨ p2) ∨ ((p3 → ((p4 ∧ p5) → False)) → True)) ∨ (False ∨ False)) ∨ p1) → p4) ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681881532482176079975922811314 : (((((p5 ∨ ((False ∧ p5) ∧ (p5 ∨ ((False ∨ p5) ∨ (False ∨ (True ∧ (p1 ∧ p2))))))) ∧ p3) ∧ ((p3 ∧ True) → ((p3 ∧ p5) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337491717104513015315333702230 : (p1 → (((((p2 ∨ p4) ∧ True) → (p4 ∨ (p5 ∧ p4))) ∨ ((p3 → ((p2 ∧ p3) ∧ False)) ∨ (p1 ∨ p3))) ∧ (True ∨ ((p4 ∨ True) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337974495931883305553256128310 : (p1 → ((((p3 ∧ True) → (((p2 ∨ p1) ∨ True) → (p2 ∨ True))) → p5) → (p1 ∧ (((p3 → p1) → (p2 → (p4 ∨ (False ∧ p4)))) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241537900247515421710177663732 : ((False → p3) ∧ ((p4 ∧ (p4 → (((p4 ∧ p5) → p2) ∧ ((False → (p1 ∧ p3)) → False)))) ∨ (p3 → (p2 → (p2 ∨ ((p1 ∨ p3) ∧ p1)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122096921117959752442141742109 : (((p5 → (((p1 → ((((p1 → True) ∧ p4) → p4) ∧ (p5 ∧ False))) → p2) ∨ ((p3 ∨ False) ∧ ((p3 ∧ False) ∨ p1)))) → True) → (p2 → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174146206828713541517410487389 : ((((p4 ∨ ((False ∨ p1) ∧ ((p1 ∨ p5) ∧ (p2 ∨ p2)))) → p1) ∨ (p1 ∧ p2)) → ((True ∨ p5) ∧ (((p2 → p1) ∧ p5) ∨ (False → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_771597024734304575116261840 : (((p5 → p5) ∧ ((False ∧ (p5 → ((True ∨ p1) → p2))) ∨ (p4 ∧ (p2 ∨ (p2 ∨ (((p5 ∧ p1) ∧ (p1 ∨ p5)) ∨ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_994338719845434851941696145699 : (((p5 ∧ (((((p4 → (False ∧ p5)) ∨ (((False ∨ (True ∧ True)) ∨ p3) ∨ p5)) → (p1 ∨ (True → (p4 → p5)))) ∧ (p4 → p5)) → False)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((p4 → (False ∧ p5)) ∨ (((False ∨ (True ∧ True)) ∨ p3) ∨ p5)) → (p1 ∨ (True → (p4 → p5)))) ∧ (p4 → p5)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- False on the left can always be used.
            apply False.elim h12
          case inr h13 =>
            -- Conjunctions on the left can always be decomposed.
            let h14 := h13.left
            let h15 := h13.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h16
            -- Implications on the right can always be decomposed.
            intro h17
            -- One of the premise coincides with the conclusion.
            exact h2
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h19
          -- Implications on the right can always be decomposed.
          intro h20
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h22
        -- Implications on the right can always be decomposed.
        intro h23
        -- One of the premise coincides with the conclusion.
        exact h21
    -- Implications on the right can always be decomposed.
    intro h24
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h25 := h3 h4
  -- False on the left can always be used.
  apply False.elim h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721512888008373642916622889477 : ((((p3 ∧ ((False ∨ p1) ∨ p1)) → (((p2 → (False ∧ True)) ∨ ((p1 → p2) ∨ p4)) ∨ ((p2 ∧ (False → (p2 ∨ (p4 ∧ p5)))) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166244972238196347189476509809 : ((p3 ∧ (((p5 ∨ ((p5 ∧ (p1 ∧ p4)) ∨ p1)) ∧ ((p4 ∧ False) ∧ (p4 ∧ True))) ∧ p5)) ∨ ((False → ((p4 ∧ p3) ∧ p1)) ∨ (p2 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191222890520587343571694307576 : (((False ∨ (p1 ∨ True)) → ((p4 ∧ (p3 ∨ p2)) ∧ False)) ∨ (p4 → ((((((False ∧ p3) ∨ p5) → p1) ∨ (p5 ∨ (p5 ∧ p1))) ∧ True) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209496217711236008287592254617 : ((p3 → (p5 ∨ (p4 → (p5 ∧ p4)))) → (False ∨ ((p3 ∧ ((p3 → (p5 ∨ (p4 ∨ (p3 ∧ (True ∧ (p5 ∧ p3)))))) → p2)) → (p2 → p2)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157018844537144127226350546103 : ((((p4 ∧ p5) ∧ (p3 ∨ (((True ∧ p1) → (((p3 ∨ True) → (p4 ∧ True)) ∧ True)) → p3))) ∨ p4) ∨ ((p4 ∨ (p5 → p4)) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339792549579513392015525232794 : (p1 → (p5 ∨ (((True → p5) ∧ ((((((p4 → (p1 ∨ p3)) ∧ p5) ∨ p5) → (p2 ∨ p1)) ∨ p2) ∨ (False → ((True → p2) ∨ p1)))) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h7
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h11 := h3 h10
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h13
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356025217919595930921020716749 : (p5 → (((p5 → (((p1 ∨ (((False ∨ p4) → p3) ∨ p3)) ∧ (p4 → p1)) ∧ p4)) ∧ (p1 ∧ (p1 ∨ p5))) ∨ (p1 → (False → (p1 ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41209528289731863521811231139 : ((((p4 → ((((p3 ∧ ((p1 ∧ p3) ∧ p1)) → (p5 ∧ (p3 ∧ (False ∧ True)))) ∨ True) ∧ (p4 ∧ p5))) → ((False → p4) → p4)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181218463352267312317857695707 : ((p2 ∧ (p2 ∨ (True → ((p4 ∨ ((p4 ∨ (p5 ∨ False)) ∧ p5)) → p2)))) → ((True → (p4 ∧ p1)) → ((False → ((p5 ∨ p4) ∨ False)) → p4))) := by
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
  cases h5
  case inl h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215263780737916557564856861904 : ((False ∧ (False ∨ (p2 → p3))) ∨ (p5 ∨ (p5 → (p3 ∨ ((False ∧ p4) ∨ (False → ((p2 ∨ True) ∧ (p1 ∨ (p5 → ((p5 ∧ p1) → p1)))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88089275061327250993057090965 : (((((False ∨ p5) ∨ p2) → p5) ∧ ((p5 ∨ p2) ∧ (((p1 ∧ p4) ∧ True) → (p2 ∨ (p1 → (((p2 ∧ p2) → (p3 ∨ p1)) ∨ p3)))))) → p5) := by
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
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : ((False ∨ p5) ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207102307756390903563548204517 : (((p1 ∨ ((p3 ∧ p4) ∨ p1)) ∧ True) → (((p4 ∧ False) → p2) ∧ (p4 ∨ (p2 → ((p3 ∨ (p1 → p4)) ∨ (False → (p4 → (p2 → True)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Implications on the right can always be decomposed.
      intro h19
      -- Implications on the right can always be decomposed.
      intro h20
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22064930823424190683848917855 : (((((p4 ∨ (p2 ∨ False)) ∧ (p4 ∧ False)) ∨ True) ∨ ((((True → p1) ∧ p3) ∨ (p1 → (p5 → p5))) ∨ ((p2 → p5) ∧ (p3 → False)))) ∧ True) := by
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
theorem thm_5_vars_216768233449967889973386273499 : ((((p5 → p1) → True) ∧ p4) → ((((p2 ∧ p2) → ((p2 ∨ ((p3 ∨ p1) ∧ p2)) ∧ p1)) ∧ p1) → ((True → p2) ∨ (True ∧ (p1 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
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
theorem thm_5_vars_135760740041017784955300512426 : (((p3 ∨ ((p1 ∧ (False ∧ p3)) ∧ ((p4 ∧ p5) ∨ ((p1 ∧ p5) ∧ p4)))) ∨ ((p5 → ((p1 ∧ p5) ∧ True)) → True)) ∨ (p1 ∧ (True ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55795408665269861307543891788 : ((((p3 ∨ p5) ∨ (True → p5)) ∧ (((p5 ∨ p5) ∨ ((p5 ∧ p2) → p1)) ∨ (p2 ∧ (((p2 → p1) ∨ p3) ∧ (p3 ∨ (p4 → True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651245965716307936447118274237 : ((((((p5 ∨ True) ∨ p5) ∧ (p1 ∧ ((p3 → (True ∧ ((p5 ∧ (p3 ∧ True)) ∨ (((p2 ∧ False) ∧ p3) ∧ False)))) ∧ p2))) ∧ (False → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655610385096152332665712812219 : (((((p5 ∧ (p2 ∧ ((((((p3 ∧ p4) ∧ p4) ∨ p4) ∨ p3) ∨ (p2 ∧ (p2 → (True ∧ p4)))) ∨ p3))) → (False ∧ p2)) ∨ (False → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666004392932856158387696720524 : (((((p1 ∨ (p5 → (p4 → (p1 → (((((False → ((True ∨ p5) → True)) → False) ∨ p2) ∨ False) → p1))))) → p1) ∧ (p2 ∨ (False → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328632759170332800307528764695 : (True → ((((True ∧ (p4 → (p1 ∧ ((p3 ∧ (p4 → False)) ∨ p1)))) → p5) ∧ p1) → ((((True → (p3 ∨ p3)) → False) ∨ (p3 ∨ p1)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319048942092570710043115712187 : (p4 ∨ (((p2 → (p5 ∧ (p3 → p1))) ∧ ((((p5 → ((p4 ∨ (False → p5)) ∨ p3)) ∨ p2) → p1) → p2)) ∨ (p1 ∨ ((False ∧ True) → False)))) := by
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
theorem thm_5_vars_620219692167229978541936613024 : (((((p4 ∧ p2) ∨ ((((False ∧ ((p4 ∨ p1) ∧ (p4 ∧ p2))) → p4) → (((False ∨ False) → ((p5 ∧ p3) → p5)) ∧ p1)) → p3)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_149669240026245582775618225985 : ((p4 ∧ (p2 → ((((p4 ∨ ((False ∧ (p5 → False)) → (False ∧ p5))) ∧ (True ∧ p3)) ∨ (p2 ∧ False)) ∧ p5))) ∨ (((p3 ∨ p4) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357104592594295462526375281448 : (p5 → ((True ∨ (True ∨ p5)) → ((((p1 ∨ (p3 ∧ p3)) → ((p2 → p1) ∧ p4)) → False) → (((p2 ∧ p5) ∧ p4) ∨ ((p3 ∨ p5) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53940250656210878807125464907 : (((p1 → (p3 ∧ (p1 ∧ (((p5 ∧ p3) ∧ p5) ∧ p4)))) ∨ ((True ∧ ((p4 ∧ (False ∨ (False → True))) ∧ ((p2 → True) ∨ False))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



