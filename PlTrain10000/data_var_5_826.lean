variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245722284314786466088025413666 : ((p3 ∧ p2) ∨ (((p1 → (p4 ∨ (((((p1 ∨ p4) ∧ p5) → p2) ∧ p4) ∧ (True ∧ ((p3 → p3) ∧ p4))))) ∧ p5) ∨ (p4 → (p4 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350171751572931958324059488251 : (p4 → (((False ∧ ((p3 ∧ p3) ∨ (p2 ∧ p5))) ∨ ((False ∨ False) ∨ ((((p3 → p5) ∧ p5) ∨ p4) ∨ ((True ∧ p5) → (p4 ∧ p3))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62619255012739713187301526859 : ((p4 ∧ (((((p5 ∨ p2) → p5) ∨ (((True ∨ p4) ∧ ((p4 → (p1 ∧ False)) → ((True ∧ True) → False))) ∧ p5)) → (p3 → p2)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226559766030507967391717408989 : (((p4 → p1) ∨ p3) ∨ (((((p5 ∨ p1) ∨ (p2 ∨ ((p2 → (p4 ∧ ((p3 ∨ False) ∧ p1))) ∨ p2))) ∧ p3) ∧ ((False → True) → False)) → p4)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h8 : (False → True) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h8
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : (False → True) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h14 := h3 h12
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h17 : (False → True) := by
        -- Implications on the right can always be decomposed.
        intro h18
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h19 := h3 h17
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h22 : (False → True) := by
          -- Implications on the right can always be decomposed.
          intro h23
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h24 := h3 h22
        -- False on the left can always be used.
        apply False.elim h24
      case inr h25 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h26 : (False → True) := by
          -- Implications on the right can always be decomposed.
          intro h27
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h28 := h3 h26
        -- False on the left can always be used.
        apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214321139963762643103686635491 : (((False ∨ (False → p1)) → p5) ∨ ((p3 ∧ False) ∨ ((p5 ∨ (p2 ∨ p3)) → (p5 ∨ (p3 → (((p3 → (p3 → (p4 ∨ p3))) ∨ True) ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346866794789982499330714967705 : (p3 → ((((False → ((((p1 ∧ p2) ∨ True) ∨ True) → ((False ∨ p4) ∨ p5))) → p1) ∨ (p3 ∨ True)) ∧ (((False ∨ (True ∧ p2)) → False) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231138563613772669461081903123 : (((p1 ∨ p3) ∨ p5) → ((p5 → ((True ∧ (p4 ∧ ((p5 → p2) ∧ ((p3 → p3) → True)))) → ((p3 ∨ ((p5 → p5) ∨ p5)) → p2))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h5.left
        let h9 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
        have h14 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h12, we can now drive its conclusion.
        let h15 := h12 h14
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h5.left
          let h19 := h5.right
          -- Conjunctions on the left can always be decomposed.
          let h20 := h19.left
          let h21 := h19.right
          -- Conjunctions on the left can always be decomposed.
          let h22 := h21.left
          let h23 := h21.right
          -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
          have h24 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h4
          -- We have shown the premise of h22, we can now drive its conclusion.
          let h25 := h22 h24
          -- One of the premise coincides with the conclusion.
          exact h25
        case inr h26 =>
          -- Conjunctions on the left can always be decomposed.
          let h27 := h5.left
          let h28 := h5.right
          -- Conjunctions on the left can always be decomposed.
          let h29 := h28.left
          let h30 := h28.right
          -- Conjunctions on the left can always be decomposed.
          let h31 := h30.left
          let h32 := h30.right
          -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
          have h33 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h4
          -- We have shown the premise of h31, we can now drive its conclusion.
          let h34 := h31 h33
          -- One of the premise coincides with the conclusion.
          exact h34
    case inr h35 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h36
      -- Implications on the right can always be decomposed.
      intro h37
      -- Implications on the right can always be decomposed.
      intro h38
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h39 =>
        -- Conjunctions on the left can always be decomposed.
        let h40 := h37.left
        let h41 := h37.right
        -- Conjunctions on the left can always be decomposed.
        let h42 := h41.left
        let h43 := h41.right
        -- Conjunctions on the left can always be decomposed.
        let h44 := h43.left
        let h45 := h43.right
        -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
        have h46 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h36
        -- We have shown the premise of h44, we can now drive its conclusion.
        let h47 := h44 h46
        -- One of the premise coincides with the conclusion.
        exact h47
      case inr h48 =>
        -- Disjunctions on the left can always be decomposed.
        cases h48
        case inl h49 =>
          -- Conjunctions on the left can always be decomposed.
          let h50 := h37.left
          let h51 := h37.right
          -- Conjunctions on the left can always be decomposed.
          let h52 := h51.left
          let h53 := h51.right
          -- Conjunctions on the left can always be decomposed.
          let h54 := h53.left
          let h55 := h53.right
          -- We want to use the implication h54 based on <expert-advice>. So we show its premise.
          have h56 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h36
          -- We have shown the premise of h54, we can now drive its conclusion.
          let h57 := h54 h56
          -- One of the premise coincides with the conclusion.
          exact h57
        case inr h58 =>
          -- Conjunctions on the left can always be decomposed.
          let h59 := h37.left
          let h60 := h37.right
          -- Conjunctions on the left can always be decomposed.
          let h61 := h60.left
          let h62 := h60.right
          -- Conjunctions on the left can always be decomposed.
          let h63 := h62.left
          let h64 := h62.right
          -- We want to use the implication h63 based on <expert-advice>. So we show its premise.
          have h65 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h36
          -- We have shown the premise of h63, we can now drive its conclusion.
          let h66 := h63 h65
          -- One of the premise coincides with the conclusion.
          exact h66
  case inr h67 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h68
    -- Implications on the right can always be decomposed.
    intro h69
    -- Implications on the right can always be decomposed.
    intro h70
    -- Disjunctions on the left can always be decomposed.
    cases h70
    case inl h71 =>
      -- Conjunctions on the left can always be decomposed.
      let h72 := h69.left
      let h73 := h69.right
      -- Conjunctions on the left can always be decomposed.
      let h74 := h73.left
      let h75 := h73.right
      -- Conjunctions on the left can always be decomposed.
      let h76 := h75.left
      let h77 := h75.right
      -- We want to use the implication h76 based on <expert-advice>. So we show its premise.
      have h78 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h68
      -- We have shown the premise of h76, we can now drive its conclusion.
      let h79 := h76 h78
      -- One of the premise coincides with the conclusion.
      exact h79
    case inr h80 =>
      -- Disjunctions on the left can always be decomposed.
      cases h80
      case inl h81 =>
        -- Conjunctions on the left can always be decomposed.
        let h82 := h69.left
        let h83 := h69.right
        -- Conjunctions on the left can always be decomposed.
        let h84 := h83.left
        let h85 := h83.right
        -- Conjunctions on the left can always be decomposed.
        let h86 := h85.left
        let h87 := h85.right
        -- We want to use the implication h86 based on <expert-advice>. So we show its premise.
        have h88 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h68
        -- We have shown the premise of h86, we can now drive its conclusion.
        let h89 := h86 h88
        -- One of the premise coincides with the conclusion.
        exact h89
      case inr h90 =>
        -- Conjunctions on the left can always be decomposed.
        let h91 := h69.left
        let h92 := h69.right
        -- Conjunctions on the left can always be decomposed.
        let h93 := h92.left
        let h94 := h92.right
        -- Conjunctions on the left can always be decomposed.
        let h95 := h94.left
        let h96 := h94.right
        -- We want to use the implication h95 based on <expert-advice>. So we show its premise.
        have h97 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h68
        -- We have shown the premise of h95, we can now drive its conclusion.
        let h98 := h95 h97
        -- One of the premise coincides with the conclusion.
        exact h98



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180245813704480351427047475198 : (((True ∨ ((False ∨ ((False ∨ p5) → (p5 ∧ p1))) ∨ (True ∧ p3))) → p5) → (p5 ∨ (((p3 ∨ ((p4 → p2) → (True ∧ p3))) ∧ True) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ ((False ∨ ((False ∨ p5) → (p5 ∧ p1))) ∨ (True ∧ p3))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54461596794607533046517622766 : ((((False ∨ (p2 → ((True → p3) → p4))) → p4) ∨ (p4 → (((((p4 → True) → ((False ∧ (True → p2)) ∨ False)) ∧ p5) ∨ p1) ∨ p4))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65631434830553092384862412357 : ((p4 ∨ (((p1 → ((True ∨ (True ∨ (((p3 ∨ p5) ∨ (p5 ∧ (p2 ∨ (p4 → p3)))) ∧ (True ∧ p5)))) ∨ (p1 ∨ p1))) → p5) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791847601558863337869321905713 : (((True → (((p3 ∧ (p3 ∧ ((p1 → ((p4 → False) ∧ p5)) ∧ False))) ∧ (p3 ∧ (((p3 → p2) ∨ p4) → (p1 ∧ p2)))) ∧ (p4 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164887949569384883032176073189 : (((p3 → (p5 ∧ ((p5 ∨ ((p5 → (((True ∧ p4) ∨ False) ∨ True)) ∧ True)) → False))) ∨ p3) ∨ ((p1 ∨ (False ∨ p1)) ∨ (False → (p1 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166155054411492437892381350609 : ((False ∧ ((True ∨ ((p3 → True) ∧ (((p4 ∨ (p2 → p3)) ∧ (p3 → p3)) → p2))) → p4)) ∨ (p1 → (((p3 → (True → False)) ∨ True) ∨ p3))) := by
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
theorem thm_5_vars_46986596545068978945209126654 : (((((p5 → ((((((False → p5) → False) ∧ p3) → p3) → p4) ∧ (p1 → p3))) ∧ (p4 ∧ ((False → p1) ∨ False))) → p1) ∨ (False → p4)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206832046607405432060235962792 : ((p5 → (p1 ∧ ((p1 ∨ False) ∨ True))) ∨ ((False → (p2 → (False → p5))) ∧ (((p4 ∨ (False ∧ p2)) ∧ False) ∨ (p2 → (False ∨ (False → False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45812628814514069100316621233 : (((p1 → (False → ((p5 ∧ (((p5 ∨ (False → p4)) ∨ p4) ∧ ((((((p4 ∧ p4) ∧ p3) ∧ p3) ∧ p3) → p1) → p4))) ∧ p4))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117091112598101939232063293775 : (((p1 → False) → (p1 ∨ ((False → (p2 → (p1 → ((p5 ∧ ((True → p5) ∨ p2)) ∨ p5)))) → ((p4 → p5) ∨ (False ∨ True))))) ∨ (p5 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248461024704244303719549755813 : ((p2 ∨ p5) ∨ (((p2 ∨ p4) ∨ (p1 ∨ ((False → p3) → ((p2 ∨ p3) → (p5 → True))))) ∨ (((False → (p5 ∧ False)) → (p1 ∨ p3)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227392542821614995698125465159 : (((p4 → p2) → p3) ∨ (True → (((True ∧ (p4 ∧ (True ∧ ((p2 ∧ True) ∧ (False ∧ p3))))) ∨ (p1 ∨ (True → p3))) ∨ ((p1 ∧ p4) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_738682196560130376871476349358 : ((((p2 ∧ p1) ∨ ((p4 ∨ p3) ∧ ((p2 ∨ (p5 → (((p4 ∧ (True ∧ (p5 ∨ True))) ∨ (((p2 ∨ p4) ∨ True) ∧ False)) ∧ True))) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54329406459401977269815683892 : (((p2 ∧ (False → (p5 ∧ ((p3 ∨ False) ∨ p5)))) ∧ (((p4 → (p2 → True)) ∧ (p3 ∨ ((False → False) → True))) → ((p2 ∨ p1) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717521578822604132659725828738 : ((((p2 → (False ∨ (p1 ∨ p5))) ∧ (p2 ∧ ((p4 ∨ (p3 → ((p4 ∧ (p5 ∧ False)) ∨ ((False ∧ False) ∧ ((p3 ∨ True) → p2))))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244685727606929351082213159875 : ((p1 ∧ True) ∨ ((p4 → (((p2 ∧ (p4 → ((p3 ∧ ((p3 ∨ p3) ∧ p4)) ∨ p3))) ∧ p4) ∨ (p5 → (True ∨ (p1 → True))))) ∧ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806807896756705936930223962233 : (((p4 → (((((p4 → (False ∧ p3)) → p3) ∧ p1) ∨ (p4 ∧ ((((p2 ∧ ((p5 ∧ p2) ∧ p5)) ∧ p2) ∧ p2) ∧ True))) ∨ (False → p1))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42164975247842042831321603916 : ((((p4 → p1) → (p1 ∨ (((False ∧ ((False → True) ∨ ((((p4 ∨ p3) ∧ (p2 ∨ (p2 ∧ p5))) ∨ p1) ∨ p2))) ∧ p3) ∨ p5))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201761953187949943421112052250 : ((((True → (p3 ∨ p4)) ∨ p5) ∨ True) ∧ (False ∨ (p3 → (((p1 ∧ p3) ∨ p5) ∨ ((((p2 → p4) → p1) → (True ∨ p5)) ∧ (True ∨ p5)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60567371119561962479487666198 : ((True ∧ ((((p2 ∧ ((p1 ∨ (True → False)) ∧ (((False ∨ p4) ∧ p5) → ((p3 ∧ p5) → (p4 ∨ p3))))) → (p2 → p2)) → p1) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798894595139920978366805708515 : (((p1 → ((p3 ∨ False) ∧ (p5 ∨ ((p5 ∧ p3) ∨ ((p1 ∧ ((False ∨ p1) ∧ p4)) ∧ (((False ∧ (p3 ∧ (p5 ∧ p3))) → p4) → p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300866355069995622764481642214 : (False ∨ (((True → (((p2 ∨ p5) ∨ (p2 ∨ p3)) ∨ ((p2 ∨ p2) ∨ p3))) ∧ True) ∨ (p3 ∨ ((False ∧ p5) → ((p1 ∧ True) ∨ (True → False)))))) := by
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
theorem thm_5_vars_302876925907581976938113378154 : (False ∨ (True → (((((p1 ∧ p4) ∧ False) ∧ p4) ∨ ((p5 ∨ ((False → ((p4 ∧ p4) ∨ p2)) ∨ (True → p5))) ∧ False)) ∨ ((p5 → True) ∨ True)))) := by
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
theorem thm_5_vars_47259987855699346761739839548 : (((((True ∧ (False → (False ∨ p2))) → p1) → (((p3 → ((p2 → ((False ∨ p5) → p1)) → (False ∨ p1))) → False) → p5)) ∨ (p1 ∧ p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p3 → ((p2 → ((False ∨ p5) → p1)) → (False ∨ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : (True ∧ (False → (False ∨ p2))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h6
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h3
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623698857648613685704236872359 : ((((p1 ∨ ((((p3 ∧ ((p5 ∧ p4) ∨ (False ∨ p4))) ∨ ((True ∨ (p4 ∨ p2)) → ((p3 ∨ False) → p1))) ∨ (p2 → p5)) → p1)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197026472885281031039303496152 : (((((False → p4) ∧ True) → (p3 ∧ p3)) ∨ p2) ∨ ((((p5 ∧ p4) ∧ ((p3 ∨ p2) ∨ True)) → ((True ∨ (False → p3)) ∨ True)) → (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193776414650224882655860770473 : ((p4 ∧ (((p3 → True) ∧ (p2 ∧ (p4 ∧ p1))) ∨ p5)) → (p1 ∨ (((((p1 → p3) → p2) ∧ False) ∨ ((p3 → False) ∨ (p5 ∨ p2))) ∧ p5))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166071313415932466337360331207 : (((True ∨ p3) → (p2 ∨ (p4 ∨ ((((p2 → p1) ∨ p1) → p1) ∧ ((p5 → p3) ∨ True))))) ∨ ((p5 ∧ p1) → (p4 → (p1 ∧ (True ∧ True))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178155039525700051235440156032 : ((((p5 ∨ (p4 ∧ p3)) → ((p4 ∧ (p4 ∧ (False ∧ True))) → p2)) → p2) ∨ ((p3 ∨ p1) ∨ (p3 ∨ (((p5 ∧ p1) ∨ p1) → (p1 ∧ True))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_915065472310201196861620989448 : ((((False ∨ (p5 ∧ (p1 → ((p3 ∨ ((False → p1) → p4)) ∨ ((p2 → p3) → p3))))) ∧ ((((p2 → p1) → (p4 ∨ p3)) ∨ p5) → False)) → p3) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : (((p2 → p1) → (p4 ∨ p3)) ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321369904837796627467562869405 : (p4 ∨ (True → ((((((p5 ∨ (p5 ∨ p1)) ∧ p2) ∧ p5) ∧ ((True → True) → p5)) → (p3 ∧ (True → (p5 → p4)))) → ((True → False) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61356406574206909814123815466 : ((p1 ∧ (((p4 → p4) ∧ ((((p5 ∨ False) ∨ False) ∧ (((p5 ∨ ((True → p1) ∧ p2)) ∧ p4) ∨ (p3 → (p1 ∨ p5)))) → p1)) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44465873497919678246334008886 : (((((p2 ∧ (((False ∨ (False ∧ p4)) ∧ (p4 ∧ p4)) ∧ p1)) ∧ p1) → (((False ∧ False) → True) → ((p2 ∧ p5) → (False ∧ False)))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585426642672154114364607461604 : ((((((p4 ∧ ((p3 → ((p1 → (p3 ∧ ((True → p4) → False))) ∧ ((True ∧ p4) ∧ (p3 ∧ (p5 → p5))))) ∨ True)) ∧ False) ∧ True) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807317459332048232810237409302 : (((p4 → (((p3 ∧ ((p3 → (p4 ∧ p5)) → True)) ∧ (False ∨ (p3 → p1))) ∨ ((p2 ∧ p3) ∧ (p1 ∨ (p1 → ((p4 ∨ True) ∨ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217754677175117274929189319172 : (((p4 ∧ (p4 ∧ p3)) → p4) → (((p5 → (((((p3 ∧ True) ∨ (((p3 ∧ p2) ∧ p1) ∧ p4)) ∧ p4) ∧ False) → p5)) → False) → (p3 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p5 → (((((p3 ∧ True) ∨ (((p3 ∧ p2) ∧ p1) ∧ p4)) ∧ p4) ∧ False) → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
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
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h16.left
      let h19 := h16.right
      -- False on the left can always be used.
      apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h20 := h2 h3
  -- False on the left can always be used.
  apply False.elim h20
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h21 : (p5 → (((((p3 ∧ True) ∨ (((p3 ∧ p2) ∧ p1) ∧ p4)) ∧ p4) ∧ False) → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h22
    -- Implications on the right can always be decomposed.
    intro h23
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h24.left
    let h27 := h24.right
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- False on the left can always be used.
      apply False.elim h25
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- Conjunctions on the left can always be decomposed.
      let h34 := h32.left
      let h35 := h32.right
      -- Conjunctions on the left can always be decomposed.
      let h36 := h34.left
      let h37 := h34.right
      -- False on the left can always be used.
      apply False.elim h25
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h38 := h2 h21
  -- False on the left can always be used.
  apply False.elim h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159168692563729453399311710321 : ((p1 → ((((p3 ∨ p1) → (((p3 → p4) ∨ p4) → p3)) ∧ p4) → ((p4 ∧ False) ∧ (p5 ∨ p5)))) ∨ ((True ∧ p1) → (p2 → (p5 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734410530070455369957864754800 : ((((False ∨ p5) ∧ (((p5 ∨ ((((p4 ∨ p4) ∧ False) → (False → p4)) ∧ ((p4 ∧ p1) ∨ p5))) ∨ (p5 → (p2 → (True ∧ False)))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78742003498465490865755531113 : (((((True → p4) ∧ ((p2 → p1) ∨ (p1 ∨ (p4 ∧ p5)))) ∧ (((p1 → True) → p2) ∧ (p4 ∨ ((True ∨ True) → p3)))) ∧ (p5 ∨ p2)) → p4) := by
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
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h5.left
    let h10 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h15 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h17 := h6 h16
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h19 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h20 := h6 h19
        -- One of the premise coincides with the conclusion.
        exact h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h5.left
      let h24 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h26 =>
          -- One of the premise coincides with the conclusion.
          exact h25
        case inr h27 =>
          -- One of the premise coincides with the conclusion.
          exact h25
      case inr h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h29 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h30 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h31 := h6 h30
          -- One of the premise coincides with the conclusion.
          exact h31
        case inr h32 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h33 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h34 := h6 h33
          -- One of the premise coincides with the conclusion.
          exact h34
    case inr h35 =>
      -- Conjunctions on the left can always be decomposed.
      let h36 := h35.left
      let h37 := h35.right
      -- Conjunctions on the left can always be decomposed.
      let h38 := h5.left
      let h39 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h40 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h41 =>
          -- One of the premise coincides with the conclusion.
          exact h40
        case inr h42 =>
          -- One of the premise coincides with the conclusion.
          exact h40
      case inr h43 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h44 =>
          -- One of the premise coincides with the conclusion.
          exact h36
        case inr h45 =>
          -- One of the premise coincides with the conclusion.
          exact h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_922076410340304166954334498590 : (((((((p5 ∧ (p3 ∧ p5)) → p1) → (p3 → p3)) ∨ (p3 → (False ∧ False))) → ((p5 → ((p4 → False) ∨ (p1 ∧ (True → p1)))) ∧ False)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p5 ∧ (p3 ∧ p5)) → p1) → (p3 → p3)) ∨ (p3 → (False ∧ False))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190803643323979825382007926097 : ((((p1 → True) ∧ ((p3 ∧ p2) ∨ p3)) ∨ (p1 ∨ p4)) ∨ (False → (p3 ∨ (((True ∨ p3) ∧ (p5 ∨ p1)) ∧ ((True ∧ False) ∨ (p4 ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300356193284726835994793113290 : (False ∨ (((True ∧ ((p5 → (((p2 ∨ (p1 → True)) ∧ ((p2 ∧ (p4 ∨ p3)) ∨ p5)) ∨ p3)) ∨ (p2 → p2))) ∧ True) ∨ (p4 → (p5 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62316292828056554768584958897 : ((p3 ∧ (((False ∧ (True → p5)) ∨ (False ∧ ((((False ∧ ((p4 → (p5 ∧ p2)) → (p4 ∧ p4))) ∨ False) ∧ False) ∨ True))) ∨ (p1 → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701739105012771307125924899178 : ((((False ∧ ((p2 → False) → ((p5 → (True ∨ p5)) → p5))) ∧ (((p3 ∧ ((p3 ∧ p2) ∨ (p2 ∧ p5))) ∧ (p1 ∨ p4)) → (p3 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317933210008497762726133728838 : (p4 ∨ ((p1 ∨ ((((True → (((p5 ∨ (False ∧ p5)) → p2) ∨ True)) ∨ (p1 ∨ (p2 → p4))) ∧ p2) ∧ ((p3 ∨ (p4 ∨ p3)) → p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750282536795835521115930340678 : (((True ∧ ((True ∧ (((p4 ∧ (p3 ∨ ((p1 → ((p1 ∨ p1) ∧ p3)) → (False ∨ p5)))) ∧ (p2 ∧ (True ∨ p1))) ∧ False)) ∨ (False ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224990043297410672111768817446 : (((True ∧ p2) ∧ p2) ∨ ((((p4 ∧ p1) → (p5 ∧ ((False ∧ p2) ∧ ((p4 ∧ p5) ∧ (p2 ∨ True))))) → (p2 → ((False ∨ p1) ∧ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136943794601454592764647375414 : (((p4 → p5) ∨ (p3 → ((p3 → p5) ∨ ((p1 ∨ (p2 ∨ (p3 ∧ ((p1 ∧ p1) ∨ (True ∧ (False ∨ p4)))))) ∧ False)))) ∨ ((p3 ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_388664157216539805476010287355 : ((((((p4 ∨ (p4 ∨ p4)) ∧ (((p1 ∨ p2) ∧ (p3 ∨ ((p5 ∧ p3) ∨ True))) → False)) ∧ ((p3 → p4) → (p2 ∧ (p2 → p5)))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_228829064354309097403428064396 : ((p3 ∨ (True → False)) ∨ ((p1 → ((((p2 → (p1 → p5)) ∧ p5) ∨ p4) → ((False → (((p4 ∨ p3) ∨ p4) → True)) → (True ∧ p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40658271338019473088188852059 : (((((((p3 → (p1 ∨ True)) ∨ ((p3 → (p1 ∨ False)) ∨ (True → ((p4 ∧ (p4 → True)) ∨ p5)))) ∨ p2) ∨ (False → p5)) → False) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605814709796542145708301586408 : ((((p4 → (True → (((((True → False) → ((True ∨ p5) → p3)) ∧ (((p1 → (p3 ∨ False)) ∧ p2) ∨ (True ∧ True))) ∨ True) → p1))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789875098563525992578160268487 : (((p5 ∨ ((True → (False ∧ True)) ∨ (((((p3 ∧ p5) → (((True ∧ p5) → p4) → p1)) ∨ ((p1 ∧ (p1 ∨ p3)) ∧ p2)) ∧ p4) ∨ True))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_63102866406353373973693548634 : ((p5 ∧ ((False ∨ (((p4 → False) → p5) → ((True ∨ ((True → (False ∨ p3)) → (((p1 ∨ p5) → (p2 → p5)) ∧ p4))) ∧ p4))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_502988348066274570947904231523 : (((((p1 ∨ p4) ∨ p5) → (((p1 ∨ False) ∨ (((p3 ∧ p2) ∧ p2) → (((False ∧ p5) ∨ p4) ∧ (p2 ∧ (p1 → (p5 ∨ p1)))))) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173325160681274072087595143889 : ((p2 → ((p3 ∧ ((p2 ∨ p2) ∧ ((p3 ∨ p3) ∨ (True ∧ p3)))) ∨ (p4 ∨ p3))) ∨ (True ∧ (p3 → (p2 → (((p3 ∧ p4) → p4) ∨ p2))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262149810062263426752148216246 : (True ∧ (((((True ∧ (False → True)) ∧ (p3 ∨ ((p4 ∧ (p3 ∧ ((((p2 → True) ∨ p4) ∧ True) → p2))) → p1))) → (p2 → p4)) ∨ True) ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174197447319953288316679160777 : ((((((p4 → (False → p2)) ∧ (p3 → (False ∨ p3))) ∧ p5) ∨ True) → (p5 ∨ p1)) → ((((p3 ∧ True) ∨ (p2 → (p5 ∧ p3))) → p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141096126462243612482709171845 : ((((True → ((True ∨ p2) → (p3 ∨ p4))) ∨ p5) → (((True ∨ p5) ∨ ((p2 ∧ p4) → p1)) → ((p2 → p4) → p2))) → ((p5 → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111204198707817692675747044825 : (((((True → p3) ∨ p4) ∨ ((True ∨ (((((True ∨ True) ∧ (p1 ∨ p3)) → p4) → ((p5 → p5) ∧ True)) ∨ p1)) → p3)) ∧ p5) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657793517947148660117459872215 : ((((True ∧ (p1 ∨ (p3 ∧ (((p5 ∨ (p5 ∨ (p1 → ((p3 ∧ p5) → ((False ∧ p4) → (True ∧ False)))))) ∨ p5) → p1)))) ∨ (True → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58968739084323068680096490626 : (((p2 ∧ p3) ∨ ((((True ∨ p5) ∨ p3) ∨ (((p2 ∧ False) ∧ ((True ∨ ((p4 ∨ p1) ∧ (p5 ∨ (p5 → p5)))) ∨ p5)) ∨ p5)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309787482089646708283003727432 : (p2 ∨ ((((p1 ∧ (((p1 → p1) ∧ (False → ((p5 → p2) → False))) ∨ p4)) ∨ ((True → p1) ∧ p4)) → p5) ∨ (((False ∨ False) ∨ False) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117614693134157416208375105001 : ((p2 ∧ (p5 → (((p4 ∧ (p4 ∨ p1)) ∧ ((p1 ∧ ((p1 → ((True ∧ p3) → p3)) ∨ p2)) ∧ True)) ∨ (p1 → (p5 → p5))))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54045142296063454140449834476 : (((((p5 ∧ p4) ∧ (p5 ∨ p2)) ∧ (p2 → (p5 ∧ p5))) → ((False ∨ p2) ∨ ((((p5 → (False ∨ True)) ∨ p3) ∧ (p4 → p3)) ∨ p5))) ∨ p3) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115790044166971024440057973124 : (((((True → True) ∧ p3) ∨ True) ∧ ((p2 → ((p1 ∨ (((p5 ∧ (True ∨ (p1 ∨ p3))) ∧ (p4 ∨ p2)) → p5)) → False)) ∧ True)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201089777065347159913940812087 : ((p5 ∨ (p1 → ((True ∧ (p5 → True)) → p5))) → ((((True ∧ p2) ∧ p4) ∨ ((p3 → (p1 → p4)) → p5)) ∨ (((p3 ∧ True) → True) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313351462456391965361646402750 : (p3 ∨ ((p1 → (p1 ∧ ((((p5 → ((p4 → ((True → True) ∨ (p5 ∧ (p2 → p4)))) → (p1 ∧ (p5 → True)))) ∧ True) → p3) → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41429630143719694745543686876 : ((((((((p3 → (p3 → True)) ∨ p5) ∧ p4) ∧ (p3 → (False ∧ p1))) → p4) → (((p2 ∨ p3) ∨ (False ∧ (p1 → p1))) ∧ p4)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217424962443066314370048151764 : (((p2 → (True ∨ p2)) ∨ True) → ((False ∨ p4) ∨ (((p1 → p2) ∨ (p5 ∧ p4)) ∨ (((False ∧ (True → p3)) ∨ (p2 ∨ True)) ∨ (True → p2))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58473320475822742929471114334 : (((p4 ∨ True) ∧ (((((p2 → p1) ∧ True) → ((p1 → (p1 ∨ False)) ∧ True)) → ((p3 ∧ p5) → (p2 ∧ (p1 ∨ (p3 ∨ True))))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259802310067689965083496517000 : ((p1 → p3) → ((((p4 ∨ ((False ∨ ((p4 ∨ p5) ∨ p3)) ∨ ((False → p4) → False))) → ((p5 ∧ p1) ∧ False)) ∧ (p3 ∨ (p4 ∨ p4))) → p2)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : (p4 ∨ ((False ∨ ((p4 ∨ p5) ∨ p3)) ∨ ((False → p4) → False))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : (p4 ∨ ((False ∨ ((p4 ∨ p5) ∨ p3)) ∨ ((False → p4) → False))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h11
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h15 : (p4 ∨ ((False ∨ ((p4 ∨ p5) ∨ p3)) ∨ ((False → p4) → False))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h16 := h3 h15
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192825197212466110648843560995 : (((p4 → (False ∨ (p5 ∧ (p4 → (p3 ∨ p2))))) → True) → ((p3 ∨ ((((p3 → ((p3 → (True ∨ False)) ∧ p1)) ∨ False) ∨ p2) ∨ True)) ∨ p4)) := by
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
theorem thm_5_vars_57237576589473697468977021943 : ((((p1 ∧ p1) → p5) ∨ ((p3 ∧ (((True ∧ True) ∧ ((p2 ∨ p2) ∧ p3)) ∧ (p2 ∨ ((p3 → p2) ∨ p4)))) ∧ ((p2 → p1) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234710692063991614863321461728 : ((p4 → (p2 ∨ True)) → (p5 → ((((((p4 ∧ ((True ∨ (p5 ∨ p1)) ∧ True)) ∨ p5) ∨ p2) ∧ p1) → ((p3 ∨ True) ∨ (True ∨ p4))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315475584646276068991812811237 : (p3 ∨ (((p1 ∧ True) → True) → ((((((p2 → False) ∧ p3) ∧ (p4 → p1)) ∨ ((p4 → p4) → p4)) → False) ∨ (False → ((False ∨ p3) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58604041464927887467184521848 : (((False → p1) ∧ ((False ∨ ((p1 → ((p5 ∧ p2) ∧ p3)) → ((((p2 ∨ (p2 → False)) ∧ p4) ∨ p5) → p5))) ∨ ((p5 ∨ p4) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41742033146437348897881942957 : ((((p5 ∨ (True → (p4 → True))) ∧ (((((p1 ∨ p2) ∧ ((p2 → (p2 → (True → p3))) ∧ False)) ∨ p4) ∧ (p2 → p4)) ∧ False)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160984292197271833639384668017 : (((p5 → (True → p3)) ∧ ((p1 ∨ p3) → (((p2 ∨ (((p4 → p3) → False) ∨ True)) → p2) → p3))) → ((p3 ∨ p1) ∨ ((p4 → True) ∨ True))) := by
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
theorem thm_5_vars_655012606869124285156672483501 : ((((((p2 → p3) ∨ (((p3 ∨ p1) → ((p2 ∧ False) ∧ ((p4 ∨ False) ∨ ((p2 ∧ p1) → True)))) ∨ (False → p2))) → p2) ∨ (p3 → p3)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_900954580151283961003610586040 : ((((p3 ∨ (((p3 → ((True ∧ (True ∧ p1)) ∨ (p4 ∨ p4))) ∨ ((p3 ∧ p3) → ((p1 → p5) ∨ True))) ∨ p1)) → ((p2 ∨ False) ∧ p4)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ (((p3 → ((True ∧ (True ∧ p1)) ∨ (p4 ∨ p4))) ∨ ((p3 ∧ p3) → ((p1 → p5) ∨ True))) ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690014839216857535630667405477 : ((((p2 ∧ (p4 ∧ ((p1 ∧ p2) ∨ ((p5 ∧ (p2 ∨ (p5 ∨ p4))) ∧ (p5 ∨ p5))))) ∨ ((p5 ∧ ((p2 ∨ (p5 ∨ p4)) → p5)) → p5)) ∨ False) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111487559649499208818051005954 : (((p2 → (False ∨ (True ∧ (((p2 → ((p1 → p3) ∨ (p4 ∧ p3))) ∧ (((p3 → True) → p5) ∧ p4)) ∧ (p3 → p5))))) ∧ p4) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165546654806525408633733982368 : ((((p4 ∨ (p1 ∧ (False ∧ p1))) ∨ (False → p1)) ∧ (p1 → (((False ∧ True) ∧ p4) ∧ p1))) ∨ (((((p3 ∨ p5) → False) ∨ p2) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150205675085995149860426825512 : ((p2 → ((p4 ∨ ((False → True) ∧ ((p1 ∧ (p4 ∧ (p3 ∧ True))) → True))) ∧ ((p1 ∧ (False ∧ p4)) ∨ p3))) ∨ (((p5 → p3) ∧ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232334142260378905075500753910 : (((p4 → True) → p2) → ((((p3 → p5) → (p1 ∨ p1)) ∨ (p5 → p5)) ∧ (p2 ∨ ((p1 ∨ (p3 → p2)) ∧ (p5 → (True ∨ (False → p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p4 → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324939954505302437537306036176 : (p5 ∨ ((p2 ∨ False) ∨ (((p1 → p5) ∧ ((p1 ∨ ((p1 ∨ p4) ∧ p2)) ∧ (((True → ((True ∨ (p4 → False)) ∨ True)) ∧ p3) ∧ p2))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230608002679400872609439499819 : (((p2 → False) ∧ p2) → ((True → False) → (p1 ∨ ((p5 → p4) → (((p4 → (p1 ∧ (((p1 → (True ∨ p2)) → p5) ∨ p5))) ∨ p2) ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68155865688107182301281605361 : ((p3 → (((p5 ∨ (False → p2)) ∧ (((((p2 → False) ∧ p1) ∧ (False ∧ ((p4 ∧ p4) ∧ p3))) ∨ p3) ∨ (False ∧ (p4 → p5)))) ∧ p3)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231990859723070106170464160572 : (((p2 ∨ p1) → p2) → ((p4 ∨ ((True ∧ (p5 ∨ ((False → p5) → (p3 → True)))) ∧ (((p1 ∨ p3) ∨ (False → p5)) ∧ (p5 ∧ True)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159952486557279915353649332818 : ((((p5 → (p3 ∧ (p5 ∧ (((p1 ∧ p4) ∧ ((p3 ∨ p1) ∨ p4)) ∧ True)))) ∨ (p3 ∨ p4)) → False) → ((((p5 ∧ p4) ∨ p2) → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676673355398163519012291109232 : ((((p4 ∧ (p3 ∨ (True → ((p5 ∧ p3) ∨ (((True ∨ True) ∨ (True → p5)) → (p4 → (p5 ∨ False))))))) ∧ (p1 → ((p4 ∧ p4) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620092637432334703391571585545 : (((((True ∧ p2) ∨ ((p3 ∨ p5) ∧ (True ∧ (True → (((True → ((False → True) → p3)) ∨ ((False ∨ True) ∨ (p1 ∧ False))) ∨ p5))))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



