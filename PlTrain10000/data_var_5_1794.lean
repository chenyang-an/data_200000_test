variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613070284180739083000175115396 : ((((((p1 ∧ ((p4 ∨ ((False → (p3 → p1)) ∧ ((True → ((p3 → p4) → p4)) → (p2 ∨ p1)))) → p4)) ∨ False) → (False ∧ p1)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_66664670153883780833532757968 : ((True → (((p3 ∨ p3) ∨ (p5 ∨ (p2 ∨ p5))) ∧ ((((((p5 ∧ False) ∨ (False ∧ p3)) ∧ (p4 ∧ True)) ∨ p5) → p5) → (p5 ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809538509787193364211584603178 : (((p5 → ((((p4 ∧ p2) ∧ ((p4 → p2) → False)) ∧ (True → (False ∨ ((p5 ∨ p3) ∨ (p1 → (False ∨ (p5 ∨ (False ∧ True)))))))) → p1)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h9 : (p4 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h11 := h6 h9
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703796628393715644775249422097 : (((((((((p2 → p2) ∧ p1) → p5) ∧ p3) ∧ p2) ∨ p5) → (False ∧ ((p5 ∧ ((((p2 → p3) → (p3 → p2)) ∨ p3) → p5)) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178952179865540032933040512830 : (((p5 ∧ p4) ∨ ((False ∧ ((((p5 ∨ p5) → True) ∧ p4) ∨ p3)) ∧ False)) ∨ (p5 ∨ (False → (((p2 ∧ (True ∧ p2)) ∨ p4) ∨ (p4 ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165407882613961171962323862347 : ((((((p1 ∧ ((True ∨ (p3 → True)) ∨ p5)) ∧ p4) → True) ∨ p1) → ((p2 ∧ p5) ∨ False)) ∨ ((((True ∨ (True ∧ False)) ∨ True) ∨ p5) ∨ p2)) := by
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
theorem thm_5_vars_136285035896552516102325000364 : ((((p3 ∨ p5) → (False ∧ (p5 → p5))) → (((p4 ∨ ((True → p2) ∧ (True → p5))) ∧ (True ∨ (p5 → p1))) ∧ p4)) ∨ ((p2 ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254412920920137469892845310840 : ((p2 ∧ p5) → ((((p1 ∨ (True ∧ p5)) → False) ∧ ((((p1 ∨ p2) ∧ p3) ∨ p4) ∧ p4)) → (p1 ∧ (p5 → ((p5 ∧ p1) ∧ (False ∧ True)))))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h1.left
      let h12 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h1.left
      let h15 := h1.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h16 : (p1 ∨ (True ∧ p5)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h17 := h3 h16
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h1.left
    let h20 := h1.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h21 : (p1 ∨ (True ∧ p5)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h20
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h22 := h3 h21
    -- False on the left can always be used.
    apply False.elim h22
  -- Implications on the right can always be decomposed.
  intro h23
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h24 := h2.left
  let h25 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h26 := h25.left
  let h27 := h25.right
  -- Disjunctions on the left can always be decomposed.
  cases h26
  case inl h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h28.left
    let h30 := h28.right
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h1.left
      let h33 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h33
    case inr h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h1.left
      let h36 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h36
  case inr h37 =>
    -- Conjunctions on the left can always be decomposed.
    let h38 := h1.left
    let h39 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h39
  -- Conjunctions on the left can always be decomposed.
  let h40 := h2.left
  let h41 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h42 := h41.left
  let h43 := h41.right
  -- Disjunctions on the left can always be decomposed.
  cases h42
  case inl h44 =>
    -- Conjunctions on the left can always be decomposed.
    let h45 := h44.left
    let h46 := h44.right
    -- Disjunctions on the left can always be decomposed.
    cases h45
    case inl h47 =>
      -- Conjunctions on the left can always be decomposed.
      let h48 := h1.left
      let h49 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h47
    case inr h50 =>
      -- Conjunctions on the left can always be decomposed.
      let h51 := h1.left
      let h52 := h1.right
      -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
      have h53 : (p1 ∨ (True ∧ p5)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h52
      -- We have shown the premise of h40, we can now drive its conclusion.
      let h54 := h40 h53
      -- False on the left can always be used.
      apply False.elim h54
  case inr h55 =>
    -- Conjunctions on the left can always be decomposed.
    let h56 := h1.left
    let h57 := h1.right
    -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
    have h58 : (p1 ∨ (True ∧ p5)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h57
    -- We have shown the premise of h40, we can now drive its conclusion.
    let h59 := h40 h58
    -- False on the left can always be used.
    apply False.elim h59
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h60 := h2.left
  let h61 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h62 := h61.left
  let h63 := h61.right
  -- Disjunctions on the left can always be decomposed.
  cases h62
  case inl h64 =>
    -- Conjunctions on the left can always be decomposed.
    let h65 := h64.left
    let h66 := h64.right
    -- Disjunctions on the left can always be decomposed.
    cases h65
    case inl h67 =>
      -- Conjunctions on the left can always be decomposed.
      let h68 := h1.left
      let h69 := h1.right
      -- We want to use the implication h60 based on <expert-advice>. So we show its premise.
      have h70 : (p1 ∨ (True ∧ p5)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h67
      -- We have shown the premise of h60, we can now drive its conclusion.
      let h71 := h60 h70
      -- False on the left can always be used.
      apply False.elim h71
    case inr h72 =>
      -- Conjunctions on the left can always be decomposed.
      let h73 := h1.left
      let h74 := h1.right
      -- We want to use the implication h60 based on <expert-advice>. So we show its premise.
      have h75 : (p1 ∨ (True ∧ p5)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h74
      -- We have shown the premise of h60, we can now drive its conclusion.
      let h76 := h60 h75
      -- False on the left can always be used.
      apply False.elim h76
  case inr h77 =>
    -- Conjunctions on the left can always be decomposed.
    let h78 := h1.left
    let h79 := h1.right
    -- We want to use the implication h60 based on <expert-advice>. So we show its premise.
    have h80 : (p1 ∨ (True ∧ p5)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h79
    -- We have shown the premise of h60, we can now drive its conclusion.
    let h81 := h60 h80
    -- False on the left can always be used.
    apply False.elim h81
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149962031399657332475762906383 : ((p4 ∨ ((((p5 ∨ ((p5 ∨ p2) ∧ ((p2 ∧ True) ∧ (p5 ∨ p1)))) → (p4 ∨ (p5 ∧ True))) → True) → False)) ∨ (False → (p1 ∨ (p2 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245568121776092122198917843982 : ((p3 ∧ True) ∨ (False ∨ ((((p5 ∧ (p3 ∨ (p5 ∧ True))) ∨ (((p1 ∨ p2) ∧ p1) ∨ ((True ∨ p1) ∨ p4))) ∨ p4) ∨ (False ∧ (p5 → p3))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314244736426098109702046831981 : (p3 ∨ (((True → (p5 → ((True ∧ ((True ∧ p5) → ((p4 → (p1 ∧ p4)) ∨ (True ∨ p4)))) ∨ p1))) → (p4 ∨ p1)) ∨ ((p1 ∨ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345561365581654777259784487949 : (p3 → (((False ∨ (False ∨ (p1 → p5))) ∨ (True ∧ (p3 ∧ ((p1 ∨ ((p4 ∧ (p5 ∨ p2)) ∨ (p1 → (p2 ∨ (p1 → p1))))) ∨ p4)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52521930729745591899507233891 : (((((p1 ∧ (p3 ∧ ((((p1 ∧ p2) → p1) ∧ True) → p3))) ∧ False) ∨ p5) ∨ (((p5 ∨ p3) ∧ (p1 → p1)) → ((p1 ∨ True) ∨ p4))) ∨ p1) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69253419418678494351909052426 : ((p5 → ((p1 ∧ (p4 → True)) → (((((True ∧ True) ∧ (False → ((p3 ∧ True) → p4))) ∧ p2) → (p2 ∧ (p3 → p4))) ∨ (False ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59052271609607992422346746022 : (((p4 ∧ p4) ∨ ((((p2 ∨ (p1 ∧ True)) ∨ ((p3 ∧ ((((True ∨ (True ∨ True)) → False) → (p4 ∨ p1)) ∧ True)) → True)) ∧ p1) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164588805495093264939769476601 : ((((p2 ∧ p4) ∨ (p3 → (((((p1 ∧ (p4 ∨ True)) ∨ p3) → True) → p2) ∨ p3))) ∧ True) ∨ ((True → ((False ∨ p2) ∧ (p2 → p1))) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_41493155242730705553574847701 : (((((((False ∧ ((p2 → (True ∧ p4)) ∨ p1)) → p3) ∨ True) → p4) → (((p4 ∧ (True ∧ (p4 → (p4 → p5)))) → p5) → False)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323276772193363786399611114938 : (p5 ∨ ((p2 → (((((p2 → p2) ∧ (p3 ∧ True)) → ((p4 ∨ False) ∧ (p3 ∨ ((False ∧ (p2 ∨ p1)) ∧ p5)))) → p5) → p1)) ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193935896908502041482164073297 : ((p2 ∨ ((p5 ∧ (p5 → ((False ∧ True) ∧ False))) ∧ p1)) → ((p1 ∧ p2) ∨ (((p3 ∧ p5) ∧ p3) ∨ ((False ∨ ((p3 ∧ p5) ∨ p3)) → p2)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121622534442710039229657261155 : ((((((((((p5 → True) ∧ (False → False)) ∧ False) ∨ False) → p5) → p5) ∨ (p1 ∨ p2)) ∨ ((p1 → p5) → (True ∧ True))) → False) → (p1 ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((((p5 → True) ∧ (False → False)) ∧ False) ∨ False) → p5) → p5) ∨ (p1 ∨ p2)) ∨ ((p1 → p5) → (True ∧ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730397639980415006244096470193 : ((((True ∧ (True → p1)) → (p2 ∨ (p5 → (((p3 → ((((((False ∨ p5) ∧ p1) → True) ∧ p4) ∧ p5) → p3)) → p4) ∨ (True ∧ p1))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165229932826407422955455682065 : ((((p2 ∧ True) ∧ ((True → p3) → (((p2 ∧ p5) ∧ p2) ∧ (p1 ∧ p3)))) ∨ (p4 ∨ p3)) ∨ (((((p3 ∧ p1) → True) ∨ p4) ∧ p3) → p3)) := by
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
theorem thm_5_vars_148719033609557420234122104151 : (((True ∧ ((((False → p2) ∨ False) ∨ False) ∨ True)) → ((p2 ∧ (p2 ∨ ((p5 → (False ∨ p1)) ∨ p3))) ∧ p5)) ∨ (((True ∨ True) → p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41814416708951141989200819919 : (((((p1 → p5) ∧ p1) ∧ ((((p5 → p4) → (p1 → (p5 → (((p4 → p2) → True) → p5)))) ∨ (p5 ∧ False)) ∧ (p2 ∧ p5))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769289394431269862291706503666 : (((p5 ∧ ((p2 ∨ p4) → ((p5 ∨ ((((p3 ∧ False) → p2) ∧ False) ∧ (p2 ∨ (p4 ∨ ((True → p4) → (True ∧ (p4 → True))))))) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199202961013435110993982124482 : (((True ∨ (False → ((p4 → p5) ∨ p1))) ∧ p3) → ((((p1 → (((p1 → (((p5 → p2) ∨ True) ∨ False)) ∨ p1) ∨ p2)) → False) → p1) ∨ False)) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p1 → (((p1 → (((p5 → p2) ∨ True) ∨ False)) ∨ p1) ∨ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h6
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : (p1 → (((p1 → (((p5 → p2) ∨ True) ∨ False)) ∨ p1) ∨ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h11
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590414287781589954711293561737 : ((((((True → p4) ∧ (((((p4 ∧ p1) ∨ p1) ∨ p5) ∨ p1) ∨ ((p4 → False) → (((p1 → (False ∧ True)) ∨ p4) ∨ p2)))) → p3) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50605476180127223207686544599 : ((((True ∨ (((((True ∧ ((p3 ∧ False) → (p5 ∧ False))) → p2) ∧ p5) ∧ p1) ∨ True)) ∨ (p3 ∧ p3)) → ((p1 ∨ (p1 ∧ p3)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41094439551948929722562535325 : (((((p4 ∨ ((True → ((((p1 ∧ p4) ∨ p2) → (True ∨ p4)) ∧ p4)) ∧ (p4 → p2))) ∨ (p2 ∨ True)) ∧ (p4 ∨ (p1 → p1))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636039897132618525631365748439 : ((((((False → p4) ∨ ((p3 → (p5 → p5)) ∨ (p3 ∨ ((p4 ∨ (p3 ∧ True)) → p5)))) ∧ (p4 ∧ ((p2 → (p5 ∧ p4)) ∧ p3))) → p4) ∨ p4) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h3.left
      let h12 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h3.left
        let h18 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h3.left
        let h23 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- One of the premise coincides with the conclusion.
        exact h22
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158516810476787493915328925135 : (((p2 ∨ p4) → ((p5 ∧ ((p5 ∨ (p3 ∧ (p5 ∧ False))) ∨ (False ∧ (True ∨ p5)))) ∧ (False ∧ True))) ∨ ((p1 ∨ True) → ((p2 → p2) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98822514672318092911349990509 : ((True → ((p1 ∧ ((True ∨ ((True ∨ False) ∧ True)) ∧ ((False → ((p2 ∨ p4) ∨ (p4 ∨ p2))) ∧ (True ∨ ((True ∧ p4) ∨ p5))))) ∧ p4)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_198646643582707508049837381690 : ((p3 ∨ ((p2 ∧ p2) ∨ ((True ∨ p1) ∧ False))) ∨ (p3 → (p1 ∨ (p3 → ((p3 ∧ False) → ((p4 ∨ p2) ∨ ((p3 ∧ p5) ∨ (p1 → p3)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37590627923924219328950740856 : ((((p4 → ((p2 ∨ ((True → ((((p3 → ((p2 ∨ p2) ∨ p4)) ∨ (p3 ∧ False)) ∧ p3) ∧ False)) ∨ (p4 ∧ p2))) → False)) ∨ p3) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644638742217202799597499528378 : ((((p1 ∨ (((p3 ∨ p4) ∨ p2) ∨ (((p2 → False) → p1) ∧ ((((p5 ∨ p2) ∧ (p5 ∨ ((True ∧ p4) ∨ True))) ∨ True) ∧ True)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260064350142658893428989169215 : ((p2 → False) → ((p1 ∧ (((p1 ∨ (p4 → p2)) ∧ p1) ∧ p4)) ∨ (((True ∧ ((p4 ∧ (p2 ∧ (p5 ∨ (False → False)))) → p5)) ∨ False) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h9
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62466765994982403167068368483 : ((p3 ∧ ((p1 ∧ p3) ∨ (((p5 ∨ (((p4 ∧ (p2 ∧ ((p1 → True) ∨ True))) ∧ (p5 ∧ p4)) ∨ p1)) ∧ (True → (False → p5))) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65566749275522089518923134576 : ((p3 ∨ (p3 → (((((p2 ∨ (((p2 ∨ p5) → p3) ∨ (p1 ∧ (False → p2)))) ∨ p1) → p5) ∧ p5) ∨ ((p3 → p3) ∧ (False ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_957555506816588329259765580292 : ((((False ∨ (p2 → p2)) → ((False → ((p3 ∧ (p3 ∧ (p2 → p1))) ∧ p3)) ∧ ((p2 ∧ ((((False → p5) ∨ True) ∨ p3) → False)) ∧ p5))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ (p2 → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : (((False → p5) ∨ True) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207194107461739978436307253565 : (((((p2 ∨ p5) → p2) ∧ p4) ∨ p4) → (False ∨ ((p1 ∨ p3) ∨ (((((p3 → p4) ∨ p2) ∧ (p2 ∨ p1)) ∧ (p2 ∨ (False → False))) → True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603665329459744820994186183142 : ((((p4 ∨ (((False ∧ (((p3 → p5) → (False ∨ ((False ∨ (p1 ∨ (p3 → ((p5 → p1) ∧ True)))) → p5))) ∨ p4)) ∨ True) ∨ p4)) ∧ True) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621611290993094080470949304455 : ((((False ∧ ((p4 → (p5 ∨ p5)) → ((p4 → False) → ((True ∨ (p3 → ((p5 ∧ p1) ∧ (p4 → ((p3 ∨ p4) ∨ p2))))) ∧ p2)))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135532193167962278182730186290 : ((((((False ∧ p3) ∨ p5) → ((((True → p3) ∧ p4) ∧ False) ∧ p4)) ∧ (p1 → p2)) ∧ ((p2 → (p3 → True)) → p3)) ∨ ((p2 ∧ p5) → p2)) := by
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
theorem thm_5_vars_345588724661219507544628934732 : (p3 → (((p5 ∧ True) ∧ ((p1 ∨ (False → (p3 → (((((p1 ∨ p4) → (True ∨ False)) → p1) ∧ p4) ∨ True)))) → ((True → False) ∨ p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328312847025944941964086895472 : (True → ((p1 → ((False ∧ ((p2 ∨ (p3 ∨ p5)) → p5)) ∨ (((True ∨ p4) → (p1 → False)) ∧ (p5 ∨ p4)))) ∨ (p2 → ((p5 ∧ p1) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60551091179118356145318727138 : ((True ∧ ((p5 ∧ (((p2 → (p4 ∨ p3)) → (p3 ∨ ((p5 → p1) ∨ p2))) ∧ (((True ∨ True) → (p1 ∧ (p5 ∨ True))) ∨ True))) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117427272450922174554506399483 : ((p1 ∧ ((((((p2 ∧ p1) ∨ ((p3 ∧ (p2 ∧ p1)) → p3)) → p3) ∧ (p1 ∨ p5)) ∧ p3) ∧ ((p1 ∧ (p2 ∧ False)) ∨ p2))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719016975455660820496727890084 : (((((p2 → p5) → (p1 → p3)) ∨ ((p3 ∨ False) → (((p1 → p5) ∨ (((p1 ∧ True) → p5) ∨ (p5 → (True → p3)))) ∨ (p5 ∨ p4)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654119150286932672621183049964 : (((((((p2 ∨ ((p4 ∧ (False ∨ p5)) ∨ (((((p3 ∧ p5) ∧ p2) ∧ p1) ∨ p2) ∧ p2))) ∨ (p5 ∨ p2)) ∧ p3) ∨ p2) ∨ (p2 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350919765454907387441581545988 : (p4 → ((((((p2 ∨ (p1 ∨ p3)) → True) ∧ p5) ∧ ((True → (p2 ∧ False)) ∨ ((False ∨ True) ∧ (p5 ∧ (p2 ∨ p3))))) ∨ p3) ∨ (p4 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231037641712671003290945172285 : (((True ∨ True) ∨ p5) → ((p2 ∨ ((True → (p3 ∨ p3)) ∨ p2)) ∨ (False ∨ ((False → (p5 ∨ p2)) ∨ (p4 → ((p5 ∨ False) → (p5 ∧ p4))))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
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
theorem thm_5_vars_110861691970035112741838089482 : (((((((p2 ∧ p3) → p1) ∧ (((p4 ∧ (False ∨ p2)) ∨ ((p2 ∨ (p1 ∨ (False ∧ True))) ∨ p2)) ∧ p1)) ∨ p2) → False) ∧ p4) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341987704466994776413975463413 : (p2 → (((True → (((p4 ∧ p1) ∨ p2) → ((((p4 ∧ p4) → p5) → p3) ∨ p4))) ∨ ((True ∧ p5) ∧ (p5 ∧ p2))) ∨ (True ∨ (p3 ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63370484791227289725994786674 : ((p5 ∧ (p4 ∧ (False ∨ (p1 ∨ ((((p5 ∧ True) ∨ False) ∨ ((((p3 ∧ p2) → p3) ∧ (p1 → (p4 → p1))) ∨ (True ∧ p5))) ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232255116201427915040154919237 : (((p2 → True) → p2) → ((((p3 ∧ (p1 ∨ (p4 ∧ (p3 ∧ (p3 → p1))))) ∨ True) ∨ ((((p4 ∧ True) ∨ p2) ∨ (p1 ∨ True)) → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165999732782124213217689893542 : (((p5 ∧ False) ∨ ((((p2 ∧ p3) ∨ ((p3 ∧ p3) → p3)) → p1) ∧ (p2 ∧ (p2 ∧ p2)))) ∨ (False → ((((p5 ∨ False) ∧ True) ∨ p1) → p1))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h1
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230354755464613765611224213919 : (((p2 ∨ p4) ∧ p2) → ((p5 ∨ (((p3 ∧ (((True → (p5 → p3)) ∨ True) ∧ p1)) ∧ False) ∨ True)) ∨ ((((p4 ∧ p4) ∨ p4) ∧ p1) → p2))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247487945818715476946070583343 : ((False ∨ p3) ∨ ((p1 ∧ (((p5 → False) ∧ (((p4 → p2) → p1) → (p3 → (p1 ∧ p3)))) ∧ False)) ∨ (p3 → (True → ((p1 → p1) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164770563459209442435850465414 : (((((p4 ∨ ((p1 ∨ (p4 → False)) ∧ p3)) ∧ p2) ∨ ((False ∧ True) ∧ (p2 ∧ True))) ∨ p3) ∨ ((p3 ∨ p4) → (True ∨ (p4 ∧ (p4 ∨ True))))) := by
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
theorem thm_5_vars_747734497418977758391757879880 : ((((False → False) → (((p5 → p4) → False) → ((False ∨ (((((False ∨ (p5 → p5)) → (True ∧ p5)) → p1) → p2) → p3)) → (p4 → p5)))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (p5 → p4) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h7
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68643877174747526273488092499 : ((p4 → (((((((p2 ∨ False) ∧ ((p1 ∨ (False ∨ (p4 → p3))) ∨ (p2 ∧ (p3 ∧ p3)))) ∨ (False → p3)) → p3) → p5) → p3) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135671403242245198398569351020 : (((p4 ∨ (p2 ∧ (((((False ∧ (p3 ∨ p1)) → p4) → False) ∨ (True ∨ False)) ∨ p4))) → ((False ∧ (p5 → False)) ∨ True)) ∨ (p1 → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337367884816359092704856321269 : (p1 → (((p2 ∨ (((p2 ∧ p2) ∧ ((False ∧ p4) → p5)) ∨ p1)) ∧ ((p3 ∨ ((p3 ∧ p5) ∧ p3)) ∧ (p3 → p5))) ∨ ((False ∧ p2) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152020592497799887429379992453 : ((((((True ∧ p5) → (p2 → False)) → (p2 ∨ p4)) ∨ p5) ∧ (True ∨ (((p1 ∧ False) ∧ False) ∨ (p5 → p4)))) → (p5 → ((False ∨ False) ∨ True))) := by
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
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Conjunctions on the left can always be decomposed.
        let h20 := h18.left
        let h21 := h18.right
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147635030858601924795888034285 : (((((True ∨ (p3 ∨ (p4 ∨ p5))) → (((((p5 ∨ p3) ∧ p3) ∨ (p2 ∨ p2)) ∧ p3) → False)) → p1) → p5) ∨ (True ∨ ((p1 ∧ p1) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219882318423873393291310624792 : ((p4 → ((p5 ∧ p3) ∧ p4)) → (((p4 → p1) ∧ p3) → ((((((p1 → (True ∧ p4)) ∨ True) → p1) ∧ p5) → p1) ∨ ((p4 → p1) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : ((p1 → (True ∧ p4)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50951180502547877658094989154 : (((((p1 ∨ (True ∧ ((p2 ∧ p5) ∧ p5))) ∨ p1) → (p1 → ((p2 → (True ∧ p3)) ∧ p2))) ∧ ((True ∧ ((p5 → False) ∨ p2)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69267950071238921734247528643 : ((p5 → ((False ∧ p3) ∨ ((((p2 → ((p2 ∨ True) ∧ p5)) → ((p3 ∨ (p5 → (((p2 ∧ p4) ∨ p1) → p5))) ∧ p2)) ∨ p5) ∧ p5))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300557798483513904288563324115 : (False ∨ (((p1 ∨ ((p1 ∨ p1) ∨ p3)) → ((p2 ∧ ((((p5 → p1) → p3) → p5) ∨ p4)) ∨ (p2 ∨ p1))) ∨ ((p3 ∧ False) ∨ (p3 ∨ True)))) := by
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
theorem thm_5_vars_310863909296298079787408279037 : (p2 ∨ ((True ∧ (p3 → p4)) → (((False → p2) ∧ ((p4 ∨ ((p3 ∧ True) ∧ ((True ∧ p2) ∧ ((p1 ∨ (p2 ∧ p3)) → p3)))) ∨ True)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116078173885802803907028165913 : ((((p5 → p5) ∧ True) ∧ ((p4 ∧ (p1 ∨ (True ∧ ((p4 → (p4 ∧ (((p1 ∨ (False → p2)) ∨ True) ∧ False))) ∨ p4)))) ∧ p5)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213825655132794595501157847769 : (((p4 ∧ (p1 → p1)) ∨ False) ∨ (p2 → (((p3 → ((False ∨ (True ∨ ((p5 → p1) ∨ p3))) ∧ p4)) ∨ ((p1 → p3) ∨ (p1 ∧ p3))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55136810504713073315916661344 : ((((p3 → (p2 ∧ (False ∨ False))) ∧ p1) ∨ (((p1 ∨ (p1 → p3)) → (p5 ∨ (False → (((p3 → p2) ∨ p4) ∨ (True ∧ p2))))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356356576955710997269883686217 : (p5 → (((p1 ∨ (p5 → (p2 → True))) → (False ∨ (((p4 → False) → p3) ∧ p2))) ∨ ((((p5 ∨ p5) → p1) ∧ ((p5 ∨ p5) ∧ p2)) → p5))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355528796280542242002568370257 : (p5 → (((((p2 → p5) → ((False ∨ p2) → ((((p5 ∨ (False → (False → p3))) ∧ p1) → p3) ∨ (True → False)))) → p4) ∧ p2) ∨ (p4 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48293254353915181968273481083 : (((p5 ∧ ((p3 ∨ ((((True ∧ False) ∨ p1) ∧ p5) ∨ True)) ∧ (((True → True) → ((p5 ∧ p5) ∧ (False ∧ p2))) ∧ True))) → (p1 ∨ p3)) ∨ False) := by
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
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h5.left
        let h18 := h5.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h5.left
      let h21 := h5.right
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h22 : (True → True) := by
        -- Implications on the right can always be decomposed.
        intro h23
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h24 := h20 h22
      -- We need to get the right conjuct of h24 based on <expert-advice>.
      let h25 := h24.right
      -- We need to get the left conjuct of h25 based on <expert-advice>.
      let h26 := h25.left
      -- False on the left can always be used.
      apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206650834840547231741063597374 : ((p1 → (False ∨ (p3 ∧ (True → p5)))) ∨ (p1 ∨ ((((p3 ∨ p1) → False) ∨ (((p4 → p2) → ((True ∨ p1) ∨ p4)) ∨ (p3 → p5))) ∨ p2))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41507823115033156368451425566 : ((((False → ((True ∧ (p3 ∨ ((p2 ∨ False) → p2))) ∨ (p5 ∧ p2))) → (((p2 ∧ (p4 ∨ p5)) → p4) ∧ (p3 ∨ (p1 ∨ p5)))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350138416169979235123395617650 : (p4 → ((((p3 ∧ ((True ∨ ((p4 ∧ (False ∨ p5)) ∧ p1)) ∨ p5)) ∧ False) ∧ ((((True ∧ ((p2 ∨ p2) ∧ p5)) ∧ p3) ∨ p2) ∧ p4)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138760877408031366479962446525 : ((((False ∧ (p5 ∧ p4)) → (p5 → ((((True → (p1 → False)) ∨ True) → p3) → (True ∧ ((p1 ∧ p1) ∨ p3))))) ∧ p4) → ((p4 → False) ∨ True)) := by
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
theorem thm_5_vars_310325474995679611906672088387 : (p2 ∨ ((((p1 ∧ (False → p2)) ∨ (p3 ∨ (False ∧ False))) → p4) → ((((False ∨ False) ∧ True) ∨ p4) → (((False ∧ (True ∧ p3)) ∨ p4) ∨ False)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311154346089061295305051329284 : (p2 ∨ ((p3 ∧ True) → ((((p3 ∧ (p2 ∧ False)) → (p3 ∨ (p5 ∧ p2))) → (False ∧ (((p2 ∧ (False ∨ True)) ∧ p1) ∨ (p2 → False)))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197034933058757613142252634250 : ((((p4 ∨ (False → p5)) → (p5 ∨ p5)) ∨ p1) ∨ (p2 → (((True ∨ p5) ∨ ((p4 ∧ p4) → True)) ∧ (p4 → ((p1 → (p1 ∧ p5)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160626189730066229678346050274 : ((((p5 ∧ ((False → p1) → p4)) ∧ (p2 → (p3 ∨ p3))) ∨ (p4 → (p3 → (True → (p4 ∨ p3))))) → (p4 → (((p1 → False) ∧ p3) → p4))) := by
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
  cases h1
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302617232798652693557275374467 : (False ∨ (p2 ∨ (((((True ∧ ((True → ((False ∧ False) ∨ ((p1 ∧ True) ∨ p3))) → ((p1 ∧ (p4 → True)) → False))) ∨ p1) ∨ False) ∨ True) ∨ p4))) := by
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
theorem thm_5_vars_38369283919174701306305835368 : (((((p5 ∧ False) ∧ ((((p2 ∨ ((True ∨ p1) ∨ p3)) → (False → p4)) → p2) ∨ True)) ∨ (False ∨ ((False ∧ (p3 → p3)) → p4))) ∧ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172732367240547362819350176889 : (((p2 → p5) ∨ (p3 ∧ (p2 ∧ ((p3 ∨ ((p2 → False) ∧ (p4 → p3))) → False)))) ∨ ((True ∨ (p5 → (((p4 ∧ p2) ∧ p4) → p2))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47233136280466783092187849588 : (((((False ∧ p1) ∧ (p2 ∧ ((p2 ∨ p4) ∧ p2))) ∨ (((p3 → (False ∨ p3)) ∧ (True → (p4 ∧ (p3 ∨ p5)))) ∧ p2)) ∨ (False → False)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650818216724393856748522627134 : (((((p3 ∧ (p4 ∧ (p1 → (True ∧ (False → False))))) ∨ ((p1 ∨ ((p4 → (p2 ∨ p3)) ∨ (p3 → (p3 ∧ p4)))) ∧ False)) ∧ (p5 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336128950308326585084336128474 : (p1 → (((((p4 ∨ True) ∧ p3) ∨ ((False ∧ (((p1 ∧ p4) → (False → p2)) ∧ (p3 ∨ (False ∨ (p4 ∨ p3))))) ∧ (p5 ∨ p2))) ∨ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185359570102341333284485059276 : ((p4 ∧ (True ∨ (False ∨ (p3 → ((False → (p2 ∧ p1)) ∨ True))))) ∨ (p4 ∨ ((True → (((p3 ∧ True) → ((p1 ∧ False) → True)) ∧ False)) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590250227619896892774456898790 : ((((((((p4 ∧ p2) → False) ∧ p2) ∨ (True → ((((p1 ∧ (((p3 → p2) → False) → p1)) ∧ (p4 → False)) → p5) ∧ False))) → p2) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357003707727731906855503541060 : (p5 → (((p3 → p5) ∧ p1) ∨ ((((p4 ∧ (((p2 ∧ ((p5 ∨ p4) ∨ True)) → p1) ∧ p1)) ∧ True) ∨ p4) ∨ ((False → (p3 ∧ False)) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149413130390297256683828242524 : ((True ∧ ((((((p5 ∨ p1) → (p3 ∨ p5)) ∨ p5) → p1) ∧ p5) ∨ (p1 ∨ (True ∧ ((p5 → True) ∨ p4))))) ∨ (p5 ∧ ((True → True) ∨ True))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57365143984732580434851652295 : (((p4 ∧ (True ∨ p5)) ∨ (p1 ∨ (((((p4 → p1) ∧ p5) ∧ True) ∧ (((p4 → False) ∧ p2) → (p1 ∧ (False ∨ True)))) ∨ (False ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323229074157245894250519853596 : (p5 ∨ (((((True ∨ True) → (True → False)) ∧ True) ∨ (((p3 ∨ (p3 ∨ p3)) ∨ ((False ∧ p5) ∧ ((p4 ∧ True) ∧ p5))) ∨ True)) ∨ (p3 ∨ p5))) := by
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
theorem thm_5_vars_351106713621501345893342854113 : (p4 → ((True ∧ (((p1 ∨ (((p1 ∨ p2) ∧ p3) ∨ (p4 ∨ p3))) ∨ ((p4 ∧ False) ∧ p5)) ∨ (p1 ∨ ((p5 ∧ p3) ∨ p2)))) → (False ∨ True))) := by
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
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Disjunctions on the left can always be decomposed.
          cases h10
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
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Conjunctions on the left can always be decomposed.
      let h20 := h18.left
      let h21 := h18.right
      -- False on the left can always be used.
      apply False.elim h21
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54322961236360926561961991384 : (((p1 ∧ ((((p3 ∨ True) ∨ p1) ∧ p2) ∨ True)) ∧ (((p4 ∧ True) ∨ (p3 ∨ ((p5 ∧ ((p5 → False) → True)) ∨ p4))) → (p5 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655031895355133725681294841610 : (((((True ∧ (((p2 ∧ p2) → ((p1 ∧ (p4 ∧ p3)) → ((((p3 ∧ p4) → p5) ∧ p4) ∧ p4))) ∨ (p3 ∧ p4))) → p1) ∨ (p1 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638999931039893955381430565635 : (((((p1 → (p1 ∨ (p4 ∨ p2))) ∧ (True ∨ (p1 → ((p1 → p3) ∧ (False ∧ (p1 ∨ (((p2 ∨ p5) → (p1 ∨ p4)) ∧ p1))))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



