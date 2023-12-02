variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354642027589036936285179778022 : (p5 → ((((((False → (p5 ∧ p2)) ∧ (p1 ∧ p5)) ∧ ((False ∨ ((p2 ∨ ((p3 ∧ False) ∨ p3)) ∧ (p5 ∧ p2))) → True)) ∨ p5) → p3) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81119272231808178112331536160 : ((((p2 → p1) ∧ (((True ∨ p4) ∧ ((((False → p2) → ((p3 ∨ p1) ∧ False)) ∧ (p1 ∨ p2)) ∧ p1)) ∧ p2)) ∧ (p4 ∧ (p1 ∨ p2))) → False) := by
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
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h3.left
      let h17 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h19 : (False → p2) := by
          -- Implications on the right can always be decomposed.
          intro h20
          -- False on the left can always be used.
          apply False.elim h20
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h21 := h13 h19
        -- We need to get the right conjuct of h21 based on <expert-advice>.
        let h22 := h21.right
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h24 : (False → p2) := by
          -- Implications on the right can always be decomposed.
          intro h25
          -- False on the left can always be used.
          apply False.elim h25
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h26 := h13 h24
        -- We need to get the right conjuct of h26 based on <expert-advice>.
        let h27 := h26.right
        -- False on the left can always be used.
        apply False.elim h27
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h3.left
      let h30 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h32 : (False → p2) := by
          -- Implications on the right can always be decomposed.
          intro h33
          -- False on the left can always be used.
          apply False.elim h33
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h34 := h13 h32
        -- We need to get the right conjuct of h34 based on <expert-advice>.
        let h35 := h34.right
        -- False on the left can always be used.
        apply False.elim h35
      case inr h36 =>
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h37 : (False → p2) := by
          -- Implications on the right can always be decomposed.
          intro h38
          -- False on the left can always be used.
          apply False.elim h38
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h39 := h13 h37
        -- We need to get the right conjuct of h39 based on <expert-advice>.
        let h40 := h39.right
        -- False on the left can always be used.
        apply False.elim h40
  case inr h41 =>
    -- Conjunctions on the left can always be decomposed.
    let h42 := h9.left
    let h43 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h44 := h42.left
    let h45 := h42.right
    -- Disjunctions on the left can always be decomposed.
    cases h45
    case inl h46 =>
      -- Conjunctions on the left can always be decomposed.
      let h47 := h3.left
      let h48 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h48
      case inl h49 =>
        -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
        have h50 : (False → p2) := by
          -- Implications on the right can always be decomposed.
          intro h51
          -- False on the left can always be used.
          apply False.elim h51
        -- We have shown the premise of h44, we can now drive its conclusion.
        let h52 := h44 h50
        -- We need to get the right conjuct of h52 based on <expert-advice>.
        let h53 := h52.right
        -- False on the left can always be used.
        apply False.elim h53
      case inr h54 =>
        -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
        have h55 : (False → p2) := by
          -- Implications on the right can always be decomposed.
          intro h56
          -- False on the left can always be used.
          apply False.elim h56
        -- We have shown the premise of h44, we can now drive its conclusion.
        let h57 := h44 h55
        -- We need to get the right conjuct of h57 based on <expert-advice>.
        let h58 := h57.right
        -- False on the left can always be used.
        apply False.elim h58
    case inr h59 =>
      -- Conjunctions on the left can always be decomposed.
      let h60 := h3.left
      let h61 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h61
      case inl h62 =>
        -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
        have h63 : (False → p2) := by
          -- Implications on the right can always be decomposed.
          intro h64
          -- False on the left can always be used.
          apply False.elim h64
        -- We have shown the premise of h44, we can now drive its conclusion.
        let h65 := h44 h63
        -- We need to get the right conjuct of h65 based on <expert-advice>.
        let h66 := h65.right
        -- False on the left can always be used.
        apply False.elim h66
      case inr h67 =>
        -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
        have h68 : (False → p2) := by
          -- Implications on the right can always be decomposed.
          intro h69
          -- False on the left can always be used.
          apply False.elim h69
        -- We have shown the premise of h44, we can now drive its conclusion.
        let h70 := h44 h68
        -- We need to get the right conjuct of h70 based on <expert-advice>.
        let h71 := h70.right
        -- False on the left can always be used.
        apply False.elim h71



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254289303133573190636759757784 : ((p2 ∧ p3) → ((((((((p1 ∨ p3) ∧ ((p2 → False) → p3)) → p1) ∨ False) → True) → p5) ∧ p2) ∨ (True ∨ (p1 ∨ (p3 ∨ (p5 ∧ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156943740492736204594138061183 : (((((((p4 ∧ False) ∨ (((p2 ∧ (p1 → p4)) → p3) ∧ True)) ∧ p2) ∧ p3) → (p3 ∧ p4)) ∨ p2) ∨ (False → ((p2 ∨ (p1 → p3)) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44473940230932807901161639497 : ((((((p4 ∨ (p4 ∨ p1)) ∨ (True → p2)) → ((p5 ∧ p2) ∧ p1)) → (p2 → ((p3 ∨ p5) ∨ (p4 → ((p3 ∧ p1) ∧ p5))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41440574611736725892650233741 : ((((p1 ∧ (((p5 ∨ ((((p1 ∧ p5) ∨ p3) ∧ True) → p2)) → p3) → p3)) → (((p1 ∨ False) → p3) ∨ (False → (True → True)))) ∨ False) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158122503793205089415297479379 : (((False → ((p3 ∨ p2) → p3)) ∧ (((p1 ∧ (p1 ∧ ((False ∧ p3) ∨ (p5 ∧ p3)))) ∧ p3) ∧ p1)) ∨ ((False ∨ (p4 → p4)) → (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137944619098906232522120215837 : ((p5 ∨ (((p3 → p3) ∧ ((False ∧ ((p3 ∧ (((((False ∨ p1) ∨ p2) ∨ False) ∧ p5) → False)) → p1)) ∧ p4)) ∧ p1)) ∨ ((False → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43978131698882993853105949350 : ((((p5 → (True ∨ (((p1 → ((((p5 ∨ p3) → False) → p2) ∨ (((True ∨ p1) ∨ p3) ∧ p5))) → p5) ∨ p3))) ∨ (p2 ∨ p4)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64383854052656221764943744089 : ((p1 ∨ ((p4 → ((p4 → ((p5 ∧ p2) ∨ ((True ∧ p1) ∧ (p2 ∨ (p2 ∨ (p5 ∨ p5)))))) ∧ (False ∧ (True → (False → p1))))) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597641400430761401074964733451 : (((((((True → False) ∨ p1) → p5) → ((((((True ∧ p5) ∧ True) → True) ∨ False) ∨ False) → (p5 ∧ ((p1 → (p1 ∧ True)) ∧ p1)))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50252818319442935468304459280 : (((((p5 ∨ p1) → (p5 → ((True → False) → (((p5 ∧ p2) ∧ p5) → (p5 ∧ (False ∨ False)))))) → p1) ∨ ((p2 ∨ (p1 ∨ p4)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138349210284083795605790679299 : ((p4 → ((True → ((((True → True) → (p4 ∨ p3)) → p5) → (((p5 ∨ p4) ∨ ((p3 ∧ p3) → p5)) → p3))) ∨ False)) ∨ ((False ∧ p1) → p3)) := by
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
theorem thm_5_vars_228619373413081005049436867678 : ((p1 ∨ (p3 → p5)) ∨ (((p3 ∨ (False ∨ (p5 → (p3 → p4)))) → (((p1 ∧ ((p3 ∧ p4) ∨ p4)) ∨ (p2 → (p5 → p3))) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63189754016056921639472328837 : ((p5 ∧ (((p1 → ((False ∨ ((False → (True ∨ (p4 ∨ p2))) → (((p3 ∧ p4) → False) → p2))) ∧ p5)) → p3) ∨ ((False → p3) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231575661666906338607816735045 : (((p5 → p4) ∨ p3) → (((((((p5 ∨ (p5 → (p2 ∧ (True ∧ p3)))) ∨ p5) ∨ p3) ∧ (False ∧ p4)) ∨ (p1 → p1)) → p3) ∨ (p3 ∨ True))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39055706043251588026208463899 : ((((p3 ∧ True) ∨ ((True ∧ (True ∨ (((p5 ∧ p3) → (p3 ∨ True)) ∨ (p3 ∧ (p3 ∧ True))))) → (((p3 ∧ p5) → False) ∧ p4))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41534250851185611539422906850 : ((((((p1 → p4) → (((False ∧ p2) ∧ p4) ∨ p3)) ∨ True) ∨ ((p4 ∧ (p3 ∧ ((((p5 ∨ p3) ∧ False) ∨ p4) ∨ p2))) ∨ p4)) ∨ p5) ∨ p2) := by
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
theorem thm_5_vars_322365395488815894689702963616 : (p5 ∨ (((p3 ∨ ((True → p3) ∧ (((False → ((((p3 ∨ (p1 → p5)) ∨ p2) ∧ p1) ∨ p1)) ∧ False) → p2))) → (p5 ∧ (False ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589041273118723803510975396988 : (((((p2 → ((True ∧ ((p4 ∧ (((p5 ∨ False) ∧ (p4 ∨ (p3 ∧ True))) ∨ (True ∨ True))) ∨ (p3 ∨ (p1 ∧ p4)))) ∧ p1)) ∨ p5) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202933532425044899538714570651 : (((p3 ∨ p5) ∨ (p5 → (p5 ∨ True))) ∧ (((True → p3) ∧ (p1 ∨ True)) ∨ ((p4 ∧ (((p5 ∧ p1) ∧ (True ∨ False)) ∨ (p2 → p5))) ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149710930877659637418462204342 : ((p5 ∧ (p1 ∨ (((((p3 ∧ ((p3 ∨ p1) ∧ p5)) → (p4 ∧ True)) ∧ ((p1 ∧ p4) ∧ p1)) → False) ∨ True))) ∨ (p2 → (True ∨ (p4 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39678315317213636421736830725 : (((p4 ∨ ((p3 → (((p3 ∨ (False → ((False ∧ True) → (True → p5)))) ∨ False) ∧ (p3 → (p3 ∧ ((False ∨ p1) → p4))))) → False)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_132856740756395029448434286178 : ((p3 ∨ (((((p3 → True) → (((((p3 ∧ False) → (p4 ∧ False)) → False) ∨ True) ∧ p2)) → False) ∧ (p1 ∨ p5)) ∨ True)) ∧ (True ∧ (p3 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52223532692204759676935491106 : (((True ∧ (((True ∨ p3) ∨ ((p2 → (p3 → (p4 ∨ p4))) → p3)) ∧ (p3 ∨ p4))) → (p3 → ((p1 ∨ (False ∨ p4)) ∨ (p3 → True)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h19 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191942881139435884425275455265 : ((True → (False ∧ (((p2 ∧ (False ∧ p5)) ∨ p5) ∧ p3))) ∨ (False ∨ (p3 → ((p2 ∧ (False → p5)) → ((p3 ∨ ((p1 ∧ False) ∨ False)) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156883579829388480897722496448 : ((((((((True → (p1 ∨ ((False ∧ p3) → (True ∨ p2)))) ∨ p5) ∨ p1) ∨ True) → False) ∨ p2) ∨ True) ∨ ((p1 ∧ False) ∨ ((p1 ∧ False) → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37850262036585383745981948348 : ((((True → (p1 → ((p5 ∧ False) ∧ (p1 ∧ (p2 → (p2 ∨ ((p2 → (((True ∧ True) → (p1 ∧ p3)) ∨ False)) ∨ True))))))) → p3) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41903168870662998569477652111 : (((((True ∧ p1) ∨ p2) → (((((p4 → (p1 ∨ ((True ∨ p5) ∨ (False ∧ p2)))) ∧ p2) → (True ∨ p4)) ∧ p2) → (p3 ∨ p4))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624390694195632194617219458032 : ((((p3 ∨ (True ∧ (((p4 ∧ (True → p3)) → p4) → ((p4 ∨ ((p2 → (True ∧ (False ∨ p3))) ∧ p3)) ∨ ((p2 ∧ True) → p5))))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697442378585720318378740819172 : ((((p1 ∧ (((True ∨ p4) ∧ ((p5 ∨ p1) ∧ p3)) → (p2 ∨ p5))) ∧ ((((p2 ∧ (False ∧ p2)) → p5) → (p5 ∨ False)) ∨ (p4 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149963080026226751222462692492 : ((p4 ∨ ((((True → (p2 → False)) ∧ (p4 ∨ (p2 ∨ p4))) ∧ (((p5 ∧ True) → p5) ∧ (p3 ∨ p3))) → p1)) ∨ (p5 ∨ (False → (p5 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198665394769748272839891442216 : ((p4 ∨ (((p3 ∧ True) ∨ (p2 ∨ p3)) ∧ p1)) ∨ ((False ∧ ((((p3 ∧ p2) ∨ p3) ∧ p2) → p4)) → (p4 ∧ ((p5 ∨ p5) → (True ∧ p2))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18414789553361749544809778413 : (((p2 ∨ ((p4 ∧ ((p1 → p4) ∨ (p3 ∧ p4))) ∧ (p5 → (((p1 ∧ p4) ∧ (p3 → p3)) ∨ False)))) → (((p4 ∨ p2) → p5) ∨ True)) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265710483349646486018415537213 : (True ∧ (p3 ∨ (((False ∨ p5) → (((p2 ∧ (p5 ∨ (p1 ∧ p4))) → (False → (False ∨ p2))) → (p5 ∧ (p2 ∧ p1)))) ∨ ((False ∧ p3) ∨ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177887131962547821525638864019 : ((((p3 ∧ ((p1 ∧ (True → False)) → (p4 → (p4 ∨ p1)))) → p1) ∨ p2) ∨ (p2 → (p4 → (False ∨ (True ∧ ((False → p4) ∨ (p5 ∧ p4))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242309540173404087374095622142 : ((p2 → p2) ∧ ((p5 ∨ ((((p1 ∨ True) → (p2 ∨ p2)) ∧ (p5 ∧ (False → (p3 ∧ False)))) ∨ (p3 → (p2 → (p2 ∧ (True → p2)))))) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47339052221251504511746512403 : ((((p1 ∨ False) ∧ ((((p2 ∨ (((p4 → p2) ∨ ((True → True) ∧ p4)) → p5)) ∨ False) → ((p5 ∧ p5) ∨ p3)) → p1)) ∨ (True → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43190127316925861034446708290 : (((((p3 ∧ p2) → (p3 → ((p1 ∧ p4) → (((True ∧ ((True ∧ ((True → p5) ∧ p3)) ∨ (p1 → p3))) → p4) ∨ p1)))) ∧ p4) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768413712601702492761452396681 : (((p5 ∧ ((((p1 → p5) ∧ (False ∧ (p1 ∧ p2))) ∧ (False ∨ (True ∨ ((p5 ∨ False) ∨ (p2 ∨ p5))))) ∨ ((False ∧ p5) ∧ (p3 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244827243043211608278889913719 : ((p1 ∧ p1) ∨ (((p2 ∨ True) ∨ p3) → (p1 ∨ (((True ∧ p4) ∧ ((p1 → ((p1 ∨ (p2 ∧ p5)) ∨ p1)) → False)) → ((p4 ∨ True) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117783950398860838862392777386 : ((p4 ∧ ((True → ((p5 → (p2 ∧ False)) ∨ ((p1 ∨ ((False ∧ (p3 ∨ False)) ∧ p3)) ∨ p2))) ∨ ((p1 → (False ∧ p5)) → p5))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230513885333549226323810826397 : (((True → p4) ∧ p4) → (((p1 → (p2 ∧ p5)) ∧ (p5 → False)) ∨ (((((True → (p1 ∨ False)) ∧ (p4 → True)) ∨ p3) ∨ False) ∨ (p5 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588613052798007521470026626604 : (((((True ∧ (((p1 ∨ ((p3 ∧ p1) ∧ p2)) ∨ ((p3 ∨ ((True ∨ p4) ∨ True)) → p4)) ∧ (((p3 ∨ p4) ∧ p1) ∨ p4))) ∨ True) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321656022157321527083733985045 : (p4 ∨ (p4 → ((((False ∨ (p1 → (p5 → (p1 → ((p2 ∨ (((p2 ∧ p1) → (p1 ∧ p1)) → (False ∨ p5))) → False))))) ∨ p1) ∨ True) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350177642611562693425170048668 : (p4 → ((((p5 ∨ (p5 → p2)) ∨ p1) ∧ (False ∨ (p5 ∨ ((((False ∧ ((True ∨ p1) ∨ True)) → p4) ∧ ((p1 ∧ p3) → True)) ∧ p1)))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133705845582730136739249887002 : ((((((p4 ∨ ((((p4 → True) ∨ False) ∧ p2) → p4)) → (p3 ∧ True)) ∨ p4) ∨ ((p1 → (True → p2)) ∨ p3)) ∧ p4) ∨ ((p4 ∧ False) → p5)) := by
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
theorem thm_5_vars_51109868443418111235395808001 : ((((((p2 ∧ ((((p1 → p2) → p2) ∧ (p3 ∧ p2)) → (p1 ∨ p1))) ∧ p3) ∧ p2) ∨ p1) ∨ ((p3 ∨ ((False ∧ p5) ∧ p2)) → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207428105435070728064074684682 : (((p1 ∨ ((True ∧ p2) ∧ p3)) ∨ p1) → ((False ∧ p2) ∨ (p5 → (((p3 → ((p3 → True) → p3)) ∧ ((p5 ∨ (True ∧ p4)) ∨ True)) → p5)))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- Implications on the right can always be decomposed.
      intro h20
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- One of the premise coincides with the conclusion.
          exact h19
      case inr h28 =>
        -- One of the premise coincides with the conclusion.
        exact h19
  case inr h29 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h30
    -- Implications on the right can always be decomposed.
    intro h31
    -- Conjunctions on the left can always be decomposed.
    let h32 := h31.left
    let h33 := h31.right
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h34 =>
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h35 =>
        -- One of the premise coincides with the conclusion.
        exact h30
      case inr h36 =>
        -- Conjunctions on the left can always be decomposed.
        let h37 := h36.left
        let h38 := h36.right
        -- One of the premise coincides with the conclusion.
        exact h30
    case inr h39 =>
      -- One of the premise coincides with the conclusion.
      exact h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67346599456822667164900409030 : ((p1 → (((p5 ∧ True) ∧ (((p1 → (p3 ∨ (p5 ∧ p3))) → ((p2 ∧ (p3 → (p5 ∨ p2))) ∧ (True → (p2 → p4)))) → p3)) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135580611217913938988507688609 : (((((((False → ((((True → p4) ∨ p2) → p2) → p1)) ∨ True) ∧ p4) ∨ True) → p2) ∨ (((p3 → False) → p4) → p5)) ∨ ((True → True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140138557385508209321589307771 : (((((p2 → (((True → p4) ∧ (p5 → False)) → True)) → ((p5 → p1) → ((p3 → p4) ∧ p1))) ∨ False) → (True ∨ p3)) → (True → (p4 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234942610702762774742376308765 : ((True ∧ True) ∧ (p3 ∨ ((((p2 ∨ ((((p1 ∧ (True ∨ p5)) ∨ (p5 → p2)) → ((True ∨ p4) → p3)) → (p3 ∨ p3))) ∨ p4) ∧ p4) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66332089966847174639956636864 : ((p5 ∨ (p2 ∧ ((((p3 ∨ p5) ∧ (True ∨ p1)) → (((p1 ∧ ((p3 ∧ p5) → p3)) ∧ ((False → False) ∧ False)) ∧ True)) ∨ (p4 → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647836184340553433697391896312 : (((((((p3 → ((p2 → (True ∧ False)) ∨ (((((p5 ∨ p1) ∨ p1) → (p1 ∧ p5)) → p2) → p4))) ∨ p4) ∨ p4) ∧ p3) ∧ (False ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42749992297214963848824680489 : (((True → ((p1 → True) → ((((p3 ∨ (False ∨ ((p1 ∧ p4) ∨ (True ∧ True)))) → p5) ∨ (((p3 → p5) ∧ p2) → p1)) ∨ p1))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686077458055455282355565158769 : (((((((p2 → p1) → (((False ∨ (p1 ∧ p3)) ∧ False) ∨ p5)) ∨ p4) ∧ ((p3 ∨ p3) ∨ p5)) → (p5 ∨ (p3 → (False ∨ (p1 → True))))) ∨ p2) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h21 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695111886878437692328580352948 : ((((((((False → ((False → False) ∧ p5)) ∨ True) ∨ (p3 ∧ p4)) → p2) ∨ p2) → ((p5 ∧ p4) ∨ ((((False ∧ True) → p3) ∧ p3) → p2))) ∨ p1) ∧ True) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (((False → ((False → False) ∧ p5)) ∨ True) ∨ (p3 ∧ p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779776737767430839598608093018 : (((p2 ∨ (((True ∧ ((p3 ∨ (True ∨ (p5 ∨ p5))) → p3)) ∨ ((((p2 ∧ (p4 ∧ True)) ∧ True) ∧ (p5 ∨ p1)) ∨ (p1 → p3))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336206673915799513076579271770 : (p1 → (((((((True → (False ∨ p5)) ∨ (p1 ∨ (((False → p5) → (p2 → (p4 ∨ p2))) → p3))) ∨ True) ∧ p1) ∨ True) → (p3 ∨ p5)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45881257932773960300791723487 : (((p3 → ((p3 → p4) ∧ (p5 → ((p5 ∧ ((p2 ∨ (p5 ∧ False)) ∧ p5)) ∨ (p1 ∨ (True → ((p2 ∨ (p1 → p4)) ∨ False))))))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214020512178120118379910378944 : ((((True ∨ p1) ∧ p3) → False) ∨ ((p5 → False) ∨ ((False ∨ ((True ∨ (False ∨ p2)) → (False ∨ (True → ((True → p1) ∨ True))))) ∧ (p4 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49576012670266471955587670005 : ((((((((p5 ∨ (p3 → False)) ∧ p2) ∧ True) → p4) ∧ ((False ∧ p2) → p2)) ∨ (p4 ∧ (p3 → (p2 ∨ p2)))) → (p5 ∨ (p2 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713258427263700240570899648670 : ((((p3 ∨ (p3 ∨ ((p3 ∨ p5) ∧ p5))) ∨ ((p4 → True) ∧ (((p1 ∧ p5) ∧ p2) → ((((True ∧ p2) → (p3 → p1)) ∨ p5) → p5)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h2.left
    let h11 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175044977238826203805152193094 : ((p2 ∧ ((p2 ∧ (((((p4 → p1) → p5) ∨ p5) → (p4 ∨ p2)) ∨ p3)) → False)) → (((p4 ∧ (p5 ∧ True)) ∧ (p1 ∧ p3)) ∧ (p3 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p2 ∧ (((((p4 → p1) → p5) ∨ p5) → (p4 ∨ p2)) ∨ p3)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h4
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : (p2 ∧ (((((p4 → p1) → p5) ∨ p5) → (p4 ∨ p2)) ∨ p3)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h9
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h15 := h10 h11
  -- False on the left can always be used.
  apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
  have h18 : (p2 ∧ (((((p4 → p1) → p5) ∨ p5) → (p4 ∨ p2)) ∨ p3)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h16
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h19
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
  -- We have shown the premise of h17, we can now drive its conclusion.
  let h22 := h17 h18
  -- False on the left can always be used.
  apply False.elim h22
  -- Conjunctions on the left can always be decomposed.
  let h23 := h1.left
  let h24 := h1.right
  -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
  have h25 : (p2 ∧ (((((p4 → p1) → p5) ∨ p5) → (p4 ∨ p2)) ∨ p3)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h23
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h26
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h27 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h28 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h23
  -- We have shown the premise of h24, we can now drive its conclusion.
  let h29 := h24 h25
  -- False on the left can always be used.
  apply False.elim h29
  -- Conjunctions on the left can always be decomposed.
  let h30 := h1.left
  let h31 := h1.right
  -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
  have h32 : (p2 ∧ (((((p4 → p1) → p5) ∨ p5) → (p4 ∨ p2)) ∨ p3)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h30
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h33
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h34 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h30
    case inr h35 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h30
  -- We have shown the premise of h31, we can now drive its conclusion.
  let h36 := h31 h32
  -- False on the left can always be used.
  apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621951027594794455986302353493 : ((((p1 ∧ (p3 ∨ (((p3 → p5) ∨ (p4 ∧ (p5 → (p3 ∨ False)))) ∧ ((p2 ∨ ((((p2 ∨ p3) ∧ p3) ∧ p3) → p5)) ∧ False)))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622042773240724073429464310058 : ((((p2 ∧ (((((p1 ∨ (p5 ∧ (p1 ∨ p3))) ∧ ((p1 ∨ p3) ∨ ((p5 ∧ ((p3 ∨ p4) → p2)) ∨ True))) → p5) → True) → p3)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_167372792403151966231925779706 : (((((p1 ∨ p3) ∨ (p1 ∧ p4)) ∨ (p5 ∨ (((p4 ∧ (False ∨ False)) ∨ p2) ∨ True))) → p1) → ((False ∧ (p1 → p2)) ∨ ((False ∨ p1) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ p3) ∨ (p1 ∧ p4)) ∨ (p5 ∨ (((p4 ∧ (False ∨ False)) ∨ p2) ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59621973771473132387601319919 : (((p5 → False) ∨ ((p5 ∧ ((((p1 → p2) ∧ (p4 ∧ p5)) ∨ ((p5 ∧ p3) ∧ (p2 ∨ p3))) ∧ p4)) ∧ (False → (p5 → (p2 ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150726381702185547432148017568 : ((((p2 ∨ (p4 ∧ (p5 ∧ (((p2 ∨ (False ∧ p2)) → (p1 ∨ (True ∧ (p2 ∨ p2)))) → p2)))) ∧ p4) ∨ p2) → ((p1 ∨ (p5 ∧ p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356162780062084240140777756080 : (p5 → (((p4 ∧ p1) ∨ (((p3 → (((True → p4) ∧ p4) → (p2 ∨ (p4 ∧ p1)))) ∧ p3) → p1)) ∨ ((p5 ∧ p4) → (p2 → (p2 ∨ p2))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352090438067858546035814012256 : (p4 → (((((p2 ∨ p5) ∨ p3) ∨ p1) ∧ p3) ∨ ((((p4 ∨ p3) ∨ (((p4 ∨ p3) ∧ p1) ∨ False)) ∧ p4) ∨ (p5 ∧ (p2 → (p1 → False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184478156739782301519964839607 : ((((p1 ∨ ((True ∧ False) ∧ (p1 ∧ p1))) ∨ p4) ∨ (True ∨ p2)) ∨ ((p4 ∨ p5) ∧ (p1 ∧ ((p5 ∧ (((True ∨ p3) ∨ p5) ∧ False)) ∧ True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64170823614481466158937261216 : ((False ∨ ((p1 ∨ p2) ∨ (((p5 ∧ p4) ∨ False) ∧ ((True ∨ p3) → (p5 ∨ ((p4 → False) ∨ (((False → p1) ∧ False) ∨ (p3 ∨ p1)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44645637375273734720053222586 : (((((True ∨ (False ∨ (False ∧ p4))) ∨ True) ∨ (((p4 ∧ (p4 ∨ ((False → p2) ∧ p2))) → (p4 ∨ p4)) ∧ (p5 → (p2 ∧ p5)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677362642615683083489199567182 : ((((((((False ∧ ((p4 ∨ (p4 ∧ ((p5 → p2) ∧ (True ∧ p5)))) → p5)) ∧ p3) ∧ p5) ∧ p4) ∨ False) ∨ ((p3 ∨ (p2 ∨ p5)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181711859626447770022900035674 : ((p5 → (False ∧ (p4 ∧ (((p2 → (True → (p4 ∨ p4))) ∧ p4) → p3)))) → ((False ∨ (p1 ∨ (((p4 → p3) ∨ p4) → False))) ∨ (p5 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743417762600238974295204467555 : ((((p5 → p2) ∨ (p3 → (((((p3 ∨ (p2 ∧ (p4 ∨ p1))) ∧ ((p5 → p3) ∨ p1)) → (p2 → p1)) ∧ p5) → ((False ∨ p2) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201257650048992621371583315822 : ((p3 → (((p4 → p1) ∧ p2) ∨ (p5 ∧ p1))) → ((p4 → ((p4 → (p5 ∨ (p2 ∧ p2))) ∨ (p4 ∧ (p1 → ((p4 → p4) ∨ p5))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146420419062427560635040635438 : ((p2 ∨ (True ∧ ((p4 ∨ ((p5 → (p3 ∧ (p2 ∧ (p3 ∧ False)))) → (False ∨ (False ∨ (True ∧ p2))))) ∨ True))) ∧ (((False ∧ False) → p4) → True)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764203782748695770131901332376 : (((p4 ∧ (((((p1 ∧ p3) ∨ (False → ((p1 ∧ ((p3 ∨ p4) → (p2 ∨ (p4 ∧ (p4 → (True → True)))))) → p4))) ∧ p3) ∧ p5) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743309844831586930433478539065 : ((((p5 → False) ∨ (((((p5 ∨ p3) ∨ ((False ∧ p5) ∨ ((((p1 ∨ p5) ∧ p2) ∧ p5) ∨ p2))) ∧ p2) → ((False ∧ p4) ∧ False)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130922114599022481237883275066 : (((p3 ∧ ((((False ∨ (p1 ∧ p1)) ∧ p3) ∨ p3) ∧ (True ∨ p5))) ∨ (False ∨ (False → (True ∨ ((p1 ∨ p4) ∨ p3))))) ∧ ((p1 ∧ p2) → p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41546934713870647798004456276 : ((((p5 ∧ ((True ∧ (True → True)) ∧ ((p2 ∨ p4) → p4))) ∨ (((True → (p3 ∨ (((p5 ∧ p1) ∨ p2) ∨ True))) ∨ p2) ∨ p3)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322502651594919266245327135107 : (p5 ∨ (((p4 → p3) → (((((((((p4 → p1) ∨ p3) ∨ p4) → p5) ∧ p1) → p4) ∧ (p4 → True)) ∧ p2) ∨ ((p2 → p5) ∧ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48996818247806103947277035966 : ((((p2 ∨ (((p3 ∨ (p1 ∨ (p4 ∧ p1))) ∨ ((p5 ∨ p3) ∧ p1)) ∧ ((p4 ∧ False) → (False → p3)))) ∨ p2) ∨ (p2 → (False → p1))) ∨ p4) := by
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
theorem thm_5_vars_39964245640928824860701193970 : (((p4 → (((p1 ∧ p4) ∨ ((True → False) ∨ p3)) ∧ ((((p3 → p1) ∧ False) ∧ (((p1 ∨ (p4 ∧ p4)) → p5) → p3)) ∧ p3))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167081388456371875527391102646 : (((((p2 ∧ p2) ∨ (p2 ∨ (p1 ∨ (p3 → (((p1 → p2) → True) ∨ p3))))) → False) ∨ p2) → (p3 ∨ ((((p2 ∧ p5) ∨ p1) ∨ True) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732789876657073120279205906080 : ((((p1 ∧ p5) ∧ (p3 → ((((p2 ∧ ((True ∧ True) ∨ True)) ∧ (p3 ∧ ((p4 → ((p5 → True) ∨ p4)) ∨ p3))) ∨ (p5 ∧ p5)) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151662134891210437408916166223 : ((((p2 → (p2 ∨ (p5 ∧ (p2 → p4)))) → ((p2 ∧ False) ∧ (p5 ∧ (False ∧ p5)))) ∧ ((True ∧ True) → p4)) → (((p3 ∨ p1) ∨ p5) → p1)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h1.left
      let h6 := h1.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h7 : (p2 → (p2 ∨ (p5 ∧ (p2 → p4)))) := by
        -- Implications on the right can always be decomposed.
        intro h8
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h9 := h5 h7
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h1.left
      let h14 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h1.left
    let h17 := h1.right
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h18 : (p2 → (p2 ∨ (p5 ∧ (p2 → p4)))) := by
      -- Implications on the right can always be decomposed.
      intro h19
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h20 := h16 h18
    -- We need to get the left conjuct of h20 based on <expert-advice>.
    let h21 := h20.left
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173061591902053066236399000584 : ((False ∨ (((p4 ∧ p1) ∧ p2) ∨ (((False ∧ False) ∨ (p1 → (p3 ∨ p3))) ∧ p4))) ∨ (((False → True) → ((False → True) → (False ∧ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113236503172145463825117369981 : ((((p4 ∧ ((p2 ∨ p2) ∨ ((p2 ∨ p3) ∧ ((True → (p4 ∨ (p5 ∨ ((True ∨ p3) ∧ False)))) → p2)))) → p3) ∧ (False → p1)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693974076924079813952955183396 : ((((((p5 ∨ p5) ∨ (p5 → (p1 ∨ ((p4 ∧ p3) ∨ p1)))) ∨ (False → p4)) ∨ ((p3 → p1) ∨ (False ∧ (p4 ∨ ((p4 → False) ∨ p3))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_668532380987347867807246874248 : ((((((((p4 ∧ p1) ∨ (p2 → True)) ∨ True) ∧ ((p1 ∧ True) → ((False ∨ ((False → False) → p5)) → p3))) ∧ False) ∨ (p5 ∨ (p2 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54165010427337852422748942259 : ((((((p3 → (p5 ∨ p4)) → p4) ∧ p3) ∧ p2) ∧ ((False → ((p2 → (False → p1)) ∨ ((p3 → (p1 → (True → p5))) ∧ p5))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134045148904801879756852577654 : (((((p4 → p5) ∧ ((False ∨ p1) ∨ ((p5 ∨ False) → (p5 → (False ∧ ((p1 → p5) → (p3 ∧ p3))))))) ∨ p1) ∨ p2) ∨ ((True → False) → False)) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740907312980951243660848092834 : ((((p3 ∨ p2) ∨ ((p5 → (p2 ∨ ((p2 ∧ (p5 ∧ p5)) ∨ (((p2 ∧ ((p1 ∨ p3) ∧ p5)) ∧ p5) ∧ ((False → p1) ∨ p5))))) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_158372795517399012971386726666 : (((p4 ∨ p4) ∧ (p5 ∧ ((((p2 → (((p2 ∨ False) ∨ False) ∧ p2)) ∧ p1) ∨ p1) ∧ (p2 ∧ p4)))) ∨ (p2 ∨ (p5 ∨ ((p1 ∧ False) → p2)))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337765985589523577883595299851 : (p1 → (((False ∨ ((p3 ∨ (p1 ∨ p4)) ∧ ((p5 → True) ∧ p3))) ∧ (p5 ∨ (p3 ∨ p3))) ∨ (((((False → False) → p1) ∧ p3) ∧ p2) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118659997529236267297314220468 : ((p4 ∨ (p1 ∨ ((((p5 → (True ∧ (p2 → True))) ∧ (p1 ∨ True)) ∧ (((p2 ∨ p3) ∧ p3) → (p1 ∧ True))) ∧ (False ∧ p3)))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



