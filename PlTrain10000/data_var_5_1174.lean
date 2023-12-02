variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111031532564303114630205226830 : ((((((p2 ∧ False) ∨ (p5 ∨ (True → ((p4 ∨ p2) ∨ ((p5 ∧ p1) ∧ p4))))) ∨ p2) ∧ ((p1 → (p2 ∨ True)) ∧ False)) ∧ True) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263998869964709681116960674319 : (True ∧ ((((((True → (p4 ∧ p2)) → p5) → False) ∨ (p5 ∧ p3)) ∧ p2) → ((p5 ∨ p4) ∨ ((((p1 ∧ p5) ∧ (p1 ∧ p3)) → True) ∨ p2)))) := by
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
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346980250892092194104767257284 : (p3 → (((p5 ∨ ((p5 ∧ (((p4 → p1) ∧ p5) ∨ p4)) ∨ p2)) ∨ ((p4 → True) ∨ p4)) ∧ ((((p4 → p5) → p1) ∧ False) → (p5 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259224957456425892603087907952 : ((False → False) → ((p4 ∨ p4) → (((p5 ∨ p2) ∨ False) → (p5 → (p3 ∨ ((p2 ∨ p5) ∧ ((((p5 ∧ True) ∨ p5) ∨ (p5 ∧ False)) → p5))))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
        -- Implications on the right can always be decomposed.
        intro h8
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- Conjunctions on the left can always be decomposed.
            let h11 := h10.left
            let h12 := h10.right
            -- One of the premise coincides with the conclusion.
            exact h11
          case inr h13 =>
            -- One of the premise coincides with the conclusion.
            exact h13
        case inr h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- False on the left can always be used.
          apply False.elim h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
        -- Implications on the right can always be decomposed.
        intro h18
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Conjunctions on the left can always be decomposed.
            let h21 := h20.left
            let h22 := h20.right
            -- One of the premise coincides with the conclusion.
            exact h21
          case inr h23 =>
            -- One of the premise coincides with the conclusion.
            exact h23
        case inr h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h24.left
          let h26 := h24.right
          -- False on the left can always be used.
          apply False.elim h26
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h27
        -- Implications on the right can always be decomposed.
        intro h29
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h30
          case inl h31 =>
            -- Conjunctions on the left can always be decomposed.
            let h32 := h31.left
            let h33 := h31.right
            -- One of the premise coincides with the conclusion.
            exact h32
          case inr h34 =>
            -- One of the premise coincides with the conclusion.
            exact h34
        case inr h35 =>
          -- Conjunctions on the left can always be decomposed.
          let h36 := h35.left
          let h37 := h35.right
          -- False on the left can always be used.
          apply False.elim h37
      case inr h38 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h27
        -- Implications on the right can always be decomposed.
        intro h39
        -- Disjunctions on the left can always be decomposed.
        cases h39
        case inl h40 =>
          -- Disjunctions on the left can always be decomposed.
          cases h40
          case inl h41 =>
            -- Conjunctions on the left can always be decomposed.
            let h42 := h41.left
            let h43 := h41.right
            -- One of the premise coincides with the conclusion.
            exact h42
          case inr h44 =>
            -- One of the premise coincides with the conclusion.
            exact h44
        case inr h45 =>
          -- Conjunctions on the left can always be decomposed.
          let h46 := h45.left
          let h47 := h45.right
          -- False on the left can always be used.
          apply False.elim h47
  case inr h48 =>
    -- False on the left can always be used.
    apply False.elim h48



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208503465986893242119894604100 : (((p2 ∧ True) → (p2 → (p1 ∧ p5))) → ((p1 ∨ (p5 ∨ (False → p3))) ∨ (((p3 ∨ True) ∧ p5) → ((p4 ∨ ((p5 → p5) ∨ p1)) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147033055685520229861062158051 : (((((((p2 → p2) → (p2 ∨ (p2 → ((True → p5) ∧ False)))) ∧ p3) → p1) → ((True → p3) → p5)) ∧ False) ∨ (True ∨ (p4 ∨ (p3 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214756996040538050468431902028 : (((p5 ∧ False) ∨ (p5 → p1)) ∨ ((p4 ∨ (False ∧ (p5 ∨ (p5 ∨ (p5 → (((p5 → (((True → False) ∧ p3) ∧ p1)) → p5) ∨ p2)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165175221694628038872148631098 : (((p5 ∧ ((p5 ∨ (p1 ∧ p2)) ∧ (((p3 ∨ p1) ∧ (p4 ∨ p4)) → p3))) ∧ (p4 ∧ False)) ∨ (((((p2 ∨ p2) ∧ False) → p1) → False) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∨ p2) ∧ False) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186136573209546088402832574342 : (((((True → p1) ∧ p4) ∨ (((p2 ∧ p3) → p1) → False)) ∨ False) → ((p2 → p4) → (((p1 ∧ (False → (False ∧ (p2 ∨ p3)))) → p3) ∨ p4))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h11 : ((p2 ∧ p3) → p1) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h15 := h7 h11
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785475818423620679857350990078 : (((p4 ∨ (((p1 → (p1 ∨ p4)) ∧ ((p5 ∨ True) ∧ (p2 → (((((p2 ∧ (False → (True ∨ p3))) → p5) ∧ p2) ∧ True) ∨ p2)))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40369940213351250028865941781 : (((((False ∨ ((((p4 ∧ ((p3 ∧ (True → p3)) ∧ (p5 → p1))) → False) → ((False ∨ (False → p2)) ∨ p4)) → p2)) → p5) ∨ True) ∨ p1) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46840788582825904110345516432 : ((((((False ∧ p3) ∧ ((True ∨ p2) ∧ True)) ∧ (p4 ∧ (p2 ∧ ((p5 → ((p5 → p4) ∧ p3)) → (p3 → True))))) ∧ p4) ∨ (False → p1)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611886948335992164239039799681 : (((((p5 → ((((p2 ∨ (p2 ∧ ((p4 ∨ p2) → p3))) ∨ p5) ∨ (p3 ∨ (p3 → p3))) → ((True ∨ True) ∨ (p2 → p5)))) → p2) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186910929053332325904717415876 : ((((p4 ∨ False) ∨ p4) ∧ ((False ∨ p2) → (p5 ∨ (p4 ∧ p5)))) → ((p1 → p2) ∨ ((p2 ∧ p1) → ((((p5 ∨ p2) ∧ p3) ∧ False) ∨ p2)))) := by
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
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66654985833838016861586233803 : ((True → (((p2 ∨ p3) ∨ ((p5 ∨ p5) ∨ (p1 ∧ p4))) ∧ ((((False ∧ p5) ∨ (False ∧ (False ∨ p1))) → ((False ∧ p1) → p4)) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311214475230370909626737600418 : (p2 ∨ ((True → p3) → (p5 → ((p5 ∨ ((p4 → p3) ∧ p4)) → (((True → (((False ∧ p2) → (True → p5)) ∧ (p1 ∧ False))) ∨ p4) ∨ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41602898125647909305670396205 : (((((p5 ∧ ((p4 ∨ p2) ∨ p2)) ∧ (p2 ∨ p3)) ∨ ((p2 → ((((True → True) → p5) ∧ ((p2 ∧ p1) ∧ p1)) ∨ p4)) ∨ True)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172197606818700395653626863405 : (((((p4 → (((p2 ∨ p5) → p2) ∨ p1)) ∧ p4) → False) → (p5 ∧ (p4 ∧ False))) ∨ ((p3 → ((p5 ∨ p5) ∨ (False ∨ p2))) → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134887175461110494563743815797 : (((p4 → (((p2 ∧ p2) ∨ (p1 → ((False ∨ (p2 → p1)) ∨ ((False ∨ p2) ∨ (p1 ∧ (p2 ∧ p3)))))) ∨ p2)) → p2) ∨ (False → (p3 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51604005893823010498651988381 : (((p4 → (p4 → (((p1 → (((p5 → p4) ∧ (p5 ∨ (p3 ∧ p4))) ∧ p3)) → True) ∧ p1))) → ((p5 ∧ (True → (p3 ∧ True))) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141071506594973334896438108163 : ((((p3 ∧ p3) ∨ (((True ∧ p5) → p4) → True)) ∨ ((p1 → ((((False → (False → p1)) → p5) ∧ p3) ∨ False)) → False)) → (p4 ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59351849716106586836182152099 : (((p5 ∨ p1) ∨ ((((p1 ∧ (p3 → (((True ∨ p2) ∨ p3) ∨ p3))) ∧ (p5 ∧ ((True ∨ p5) ∨ p5))) ∧ False) ∨ ((p3 ∧ p1) → True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174434176991325734074364968436 : ((((p4 ∧ ((p2 ∧ (True ∧ p3)) ∨ p4)) ∧ True) → (p3 ∧ ((p1 ∨ True) → p1))) → (((p1 ∨ (p1 → ((p4 ∨ p4) → p3))) ∨ False) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : ((p4 ∧ ((p2 ∧ (True ∧ p3)) ∨ p4)) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : ((p4 ∧ ((p2 ∧ (True ∧ p3)) ∨ p4)) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213204757608061375796079333278 : ((((p1 → p1) ∨ False) ∧ p5) ∨ ((((((p1 ∨ (p2 → True)) ∧ (False ∧ (p3 ∧ p1))) → ((True ∨ p4) → p1)) ∨ True) → (p4 ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667422871145977407217471207626 : (((((p4 ∨ p1) → ((((p2 ∧ ((p4 ∧ p2) → (False ∧ ((p3 ∧ p4) ∧ p2)))) ∧ p5) ∨ True) ∧ (p1 ∧ p1))) ∧ (True ∧ (True ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346148916165581609495019580093 : (p3 → ((p3 → ((p3 ∨ p4) → ((p2 ∨ (p3 → (p3 → (((((True → p2) ∨ p3) → p2) ∧ p3) → ((p5 → False) → p2))))) ∧ p5))) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p3 ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172611668600139925468459308872 : (((p1 → (p3 → p5)) → ((((p1 ∧ p1) ∧ p3) ∧ (True ∨ (p1 → True))) ∨ p3)) ∨ (False → ((p5 → ((True ∨ p1) ∧ (p3 → p5))) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810588667526608302323373077486 : (((p5 → ((p3 ∨ (p3 ∧ (p4 ∨ p4))) ∨ (((p4 → ((True ∨ (p4 → p5)) ∨ p2)) ∧ (p2 ∨ p1)) ∨ (p4 → ((p1 → p2) → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38081693668027754132940048798 : (((((p1 → False) → ((p2 → p2) ∧ (((((p3 → p3) ∧ False) → (p4 ∧ True)) ∧ (p3 ∨ (p4 ∧ False))) ∨ p1))) → (p4 → p3)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42840984945977817637388447894 : (((p2 → (((p5 ∨ ((True → (True → (p1 ∨ ((((p2 ∧ p3) ∧ False) → (True ∧ p4)) ∧ (False → p4))))) ∨ p1)) → p5) ∧ True)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777757410686212640708937219181 : (((p1 ∨ ((((p3 ∧ p1) ∨ True) ∧ (p1 → False)) ∨ ((True ∨ (True ∧ p4)) → (p4 → (((p5 → True) ∧ p2) ∨ ((p2 → p4) → p4)))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185078372686536067740582173980 : (((False ∨ p1) ∨ (((((p5 ∨ p5) ∨ False) → False) → False) → False)) ∨ (p1 ∨ ((True ∨ p5) ∧ ((p4 → ((p4 ∨ False) → p4)) ∧ (p1 → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778379680978340126482559378833 : (((p1 ∨ (p2 ∧ ((p3 → (p5 ∨ (p2 → ((p1 ∨ ((False ∧ ((((p3 ∨ p1) → p1) ∨ p4) ∨ p1)) ∧ (p3 → p2))) ∧ p1)))) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340511958256036393269926374640 : (p2 → ((((p4 ∧ p3) ∨ (p3 ∧ p5)) ∨ (((p5 ∨ ((False ∧ p1) → (((True ∧ False) ∧ p5) → (p2 ∨ (p3 ∧ p4))))) ∨ p5) ∨ False)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212686993668175357283693221357 : ((False → ((p1 ∨ p4) ∨ True)) ∧ (((True ∨ p1) ∧ (p2 ∧ ((p3 ∧ (p2 ∨ ((p3 ∨ ((False → p5) ∧ True)) → p5))) ∨ False))) ∨ (p1 → p1))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68717895706233019855837292710 : ((p4 → (((((p1 ∧ p4) ∧ p2) ∧ p3) ∨ (((p3 ∨ ((True ∧ (p4 → (False → False))) → False)) ∨ p4) ∨ p2)) ∨ (p2 ∨ (True → p1)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310314197855730253014364401903 : (p2 ∨ ((p5 ∨ (p1 ∧ ((False ∧ p4) → (True ∨ (p1 ∧ p2))))) ∨ ((p5 → (p3 ∧ p2)) ∨ (p2 ∨ (p5 → (p2 → (p5 → (True ∨ False)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198544204901580054973467915787 : ((False ∨ (p2 ∨ ((p3 ∨ (p2 → p1)) ∧ p2))) ∨ ((((((True ∨ p3) ∧ ((True → p1) ∧ True)) ∧ p4) → (p2 → False)) ∧ p2) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150628813709799274662859533337 : (((p4 ∧ ((True → ((p3 → ((p4 → False) → (((p3 ∧ p3) ∨ True) ∧ (p2 ∨ p4)))) ∧ p3)) ∧ p5)) ∧ p1) → ((p2 ∨ (False → p4)) ∧ p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h15 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h16 := h13 h15
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- One of the premise coincides with the conclusion.
  exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60910388775116320287985313764 : ((False ∧ (((((p4 ∨ False) ∨ ((p1 ∧ (p2 ∨ ((True → p2) ∧ p4))) ∨ (p3 ∧ p4))) → ((p4 ∨ False) ∧ (p4 ∨ p3))) ∨ False) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341965182342518889464701160351 : (p2 → (((p3 → (p5 ∧ ((((p4 ∧ p3) ∧ (((True → False) → p2) ∧ p3)) → (p3 ∧ p5)) → (False ∧ p4)))) ∧ False) ∨ ((p4 → p4) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248585560059917374313385889023 : ((p3 ∨ False) ∨ ((p3 ∧ ((p3 ∨ (p1 ∨ (True ∨ p2))) → (p5 ∧ p2))) → (((((False ∧ False) ∧ (True ∧ p1)) ∧ (False ∨ False)) ∧ p3) ∨ p3))) := by
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
theorem thm_5_vars_164451505839531148874416358611 : (((((((p5 → p3) ∨ p3) → (p5 → False)) → (True → ((p1 ∨ p3) → p5))) ∧ p4) ∧ p2) ∨ ((True ∨ (((p1 ∧ p1) ∨ p2) ∨ True)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232263728431109182498930941781 : (((p2 → False) → p5) → (p2 ∨ (((((p3 ∧ (p1 ∨ (True ∨ False))) ∨ p4) → (p1 → p3)) ∧ p3) → ((p5 ∨ False) ∨ (p4 → (p1 → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115727748270684936421004168402 : (((((False ∨ p2) ∧ p2) ∧ (p5 ∨ False)) → (((False ∨ (p1 ∧ (p3 ∨ ((p3 ∨ p5) ∨ p3)))) ∨ True) → (p1 → (False ∧ True)))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136646314049394014956823435258 : ((((p5 ∨ True) → False) → (p1 ∧ (False ∧ (p2 ∨ (p1 ∧ (((p3 → ((True ∨ (p5 ∨ p5)) ∧ False)) → p4) → True)))))) ∨ (p4 ∧ (p5 ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p5 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252095006537479448311963548538 : ((p4 → p2) ∨ (((((p5 → p2) ∨ (((p5 → p5) ∧ p5) ∨ False)) → (p4 ∧ ((False → ((True ∧ p1) ∨ p2)) ∨ p3))) ∨ p2) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218899341593898337097623402320 : ((p3 ∧ ((p1 ∧ p4) ∨ True)) → (((p5 ∨ p4) ∧ (((p3 ∧ (p2 → (True ∨ p1))) → (True ∧ False)) ∨ p2)) ∨ (False ∨ (p3 → (p4 → p3))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42282335670043261080134436212 : (((p1 ∧ (False ∨ ((((p5 ∨ p1) ∧ ((p3 ∨ p3) ∧ p3)) ∨ ((p1 ∨ p3) ∧ False)) ∨ (True ∧ ((p1 ∧ p1) ∧ (p4 → p2)))))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61242897811966496187579419598 : ((False ∧ (p4 ∧ (((p3 ∨ (((p5 ∨ p4) ∨ p4) ∨ (p2 → (p1 ∧ False)))) ∨ p4) ∨ (((p3 ∨ p1) ∧ (p1 ∧ p2)) → (p5 → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320430757523860678801456589414 : (p4 ∨ ((p1 ∨ p1) → (p4 ∨ ((p4 → (p1 → (((((p5 ∧ p3) ∧ (p4 → False)) → False) ∨ (p5 ∧ ((p5 ∨ p1) → p5))) ∧ False))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115438571430191304044374387072 : (((((p1 ∨ (p2 → p4)) → True) ∧ (p3 → p1)) ∨ (p4 → (((p1 → (p5 ∨ False)) ∧ p1) → (p1 → (p3 ∨ (p3 ∧ p5)))))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4389542442039668795218116136 : (p1 → (((((p1 → True) → ((p3 ∨ p3) ∨ p4)) ∨ True) → ((((True → ((False ∨ p5) → False)) → p4) → (p1 ∧ p4)) → p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244795387301666187726568050574 : ((p1 ∧ p1) ∨ (((p4 ∨ (((((False → p3) → (p4 ∧ p4)) ∨ p2) ∨ (((p3 ∧ ((p5 ∨ p3) ∨ p4)) ∨ p1) ∧ False)) → p5)) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791596831020775142699362149039 : (((True → (((((p1 ∨ (p2 ∨ (False ∨ p5))) ∨ (p5 ∧ ((p4 ∧ p5) ∧ ((p5 ∧ p5) ∨ True)))) → ((p2 → p2) → p2)) → p5) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216990725052231976814904353174 : (((p4 → (p5 → True)) ∧ p1) → ((((p4 → p4) ∧ (True ∧ (True → (p4 ∧ ((p3 ∧ p5) ∧ p1))))) → ((p1 → False) → p2)) ∧ (p1 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h10 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h11 := h3 h10
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58004502145063455610286289793 : (((True ∧ True) ∧ (p2 ∧ (((p1 ∧ p5) → (False ∧ ((p2 → (p3 → (p3 ∨ p4))) ∨ True))) → ((False ∨ p2) ∧ (p3 → (p2 ∨ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672902310134811386246828807778 : ((((((p1 ∨ (((p3 ∨ p4) → (p4 ∧ (False ∨ p1))) ∨ (p5 → (False ∧ False)))) ∨ p2) → ((p5 ∨ p4) → p1)) → (True → (p4 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54975123185979127898846622487 : ((((p2 → (p1 ∧ True)) → (p2 ∨ p5)) ∧ (p5 → ((((p1 → (p3 ∧ (p5 ∨ (p3 → False)))) ∧ ((p5 ∨ p3) ∧ p2)) ∧ True) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66227228980700559985530454640 : ((p5 ∨ ((p4 ∧ (((True → (p5 ∨ (p4 → p5))) ∨ True) → p2)) → (((p2 ∨ (p4 → (p2 ∧ False))) → p3) ∨ ((p5 → True) → p4)))) ∨ p5) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56276328808113918792971504395 : (((p4 → (False ∨ (p2 ∧ p1))) ∨ (p5 ∧ ((p1 ∨ p1) ∨ (p5 ∧ ((p1 → p1) ∨ ((p3 ∨ (False → (False ∨ (False → p5)))) → p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612256857188969882333632808935 : ((((((p1 → p4) ∧ ((p5 → p4) ∧ ((((((p5 ∧ (p5 → (p2 ∧ p1))) ∨ p3) ∨ p5) ∧ p2) ∨ p4) → False))) ∧ (p1 ∨ p5)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_174048838013996009031250326500 : (((False → (p1 ∧ (p3 ∨ (((((False ∨ p1) ∨ p3) → p1) → True) ∧ False)))) → p3) → (((((p4 ∨ False) ∨ True) ∧ (p2 ∧ p3)) ∨ p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (p1 ∧ (p3 ∨ (((((False ∨ p1) ∨ p3) → p1) → True) ∧ False)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65513518011190171007904658400 : ((p3 ∨ (False ∨ (p2 → ((p1 ∨ (p1 ∨ ((p1 ∧ (True ∧ (p4 → (p2 ∨ (p5 ∨ ((p1 ∧ p5) ∨ p1)))))) ∨ (p3 → p2)))) ∨ True)))) ∨ False) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783676954142950112044433619979 : (((p3 ∨ (((p4 ∨ (p5 ∨ (p2 → p1))) ∧ False) ∧ ((((p4 ∧ ((True ∧ (p5 → False)) ∨ False)) → p5) ∨ (p3 ∨ True)) ∧ (p5 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682049927633356503122796641180 : (((((p2 ∨ (((((p3 → True) ∧ p4) ∨ p5) ∧ (False ∨ (p2 ∨ (p4 ∨ p1)))) → p1)) ∨ p4) ∧ (((p1 → p4) ∨ (p2 ∧ False)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251115769141866354159846131789 : ((p2 → False) ∨ ((p4 → (((p3 ∨ ((False ∧ p1) ∧ (((True ∨ (p1 → False)) ∧ p4) ∧ ((p1 ∨ p4) ∧ p4)))) ∧ (True ∨ False)) ∨ p4)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149317538463616937309715281670 : (((p3 ∧ p1) → (p1 ∧ ((p4 ∨ (p3 ∧ (False ∨ (False ∨ (p3 ∧ (p2 ∨ False)))))) ∨ ((p2 ∨ True) ∨ p1)))) ∨ (((False ∧ True) → p1) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358175104783291996885347747614 : (p5 → (p3 ∨ (((True → ((p2 → (p4 → (((p2 ∨ (p2 ∨ p3)) ∨ p1) ∧ p1))) → p4)) ∨ True) ∨ (((False ∨ p3) ∧ (p4 ∨ p4)) ∨ p4)))) := by
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
theorem thm_5_vars_105436008784139768606739091933 : ((((False ∨ (((((p3 ∨ p3) ∨ p3) ∧ (True → (p4 ∨ p1))) ∧ (p4 ∨ p1)) ∨ p4)) ∧ p1) ∨ (p1 → ((p5 ∧ p4) → p4))) ∧ (p1 → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39670473118526366008636023007 : (((p4 ∨ ((False ∨ ((p2 ∧ ((((p3 ∨ p2) → p4) ∨ False) ∧ ((True ∨ True) ∧ p4))) → (False ∧ (p5 ∧ (p3 ∨ p4))))) ∧ p5)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685083015084463984740882002341 : ((((False ∨ (p5 → (p3 ∨ ((((False ∨ (p4 → ((p1 ∨ True) ∨ True))) ∨ p4) → False) → p1)))) ∨ ((((p2 ∧ True) ∧ p4) ∧ False) → p1)) ∨ p3) ∧ True) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179780405659194550598204481201 : ((((p2 → ((p3 ∨ p5) ∧ p1)) → ((p2 ∧ (p1 → p4)) → True)) ∧ p1) → ((((((p5 ∨ p1) ∧ p2) → (p4 ∧ True)) ∧ p4) → p1) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700088280459845874050194255193 : ((((((p3 ∧ p2) ∧ p3) → ((p3 → (p2 ∧ p3)) ∧ (True ∨ False))) → ((False ∨ p4) ∧ (p1 → ((p3 ∧ (p3 ∧ p4)) → (p2 ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114858788253380791431595858064 : ((((p2 → (((p3 → (True → (p3 ∨ p3))) ∧ p5) → p1)) ∧ (p5 ∨ p1)) ∨ (((p5 ∧ (True ∨ False)) ∧ p3) ∨ (p2 → p3))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638709449025964185414693795416 : ((((((p3 ∨ (p3 → True)) → (False ∨ False)) → ((((p5 ∧ (p5 ∧ (True → p2))) ∧ (True → p3)) ∧ (p2 → (p1 ∨ p1))) ∧ p3)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137836223454192187388805558084 : ((p3 ∨ (((False → ((p1 ∧ (False ∧ (p5 → p2))) → ((p3 ∨ p2) ∨ False))) ∧ p2) ∨ (p5 ∧ (p4 ∨ (p1 ∨ False))))) ∨ ((p5 ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748548548442172608334760085033 : ((((p3 → False) → (((p2 ∨ ((p5 → (((False → ((False ∧ p5) ∨ (p3 → True))) → p3) ∧ False)) ∨ True)) ∧ (p4 ∧ p2)) ∨ (False → p3))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_172231871630901000628059594954 : (((((p2 ∨ ((True → False) ∧ p3)) ∨ p5) ∨ p1) ∧ (((True ∨ p5) ∨ p4) ∧ p4)) ∨ (True ∨ (p3 → (((p1 ∨ (False ∨ p5)) → True) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166554645002094075805908737229 : ((p5 ∨ (((p3 ∨ p3) ∨ p3) ∨ ((p5 ∧ ((p3 ∨ p4) ∧ p5)) ∧ (p1 ∨ (True → p1))))) ∨ (True → ((True ∧ ((p1 → p2) ∨ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78238573765612170877601372422 : (((p3 → ((p3 → ((p5 ∧ p5) → (True ∨ p5))) → ((p4 ∧ ((p4 → ((p2 ∨ True) → p2)) ∨ p4)) ∨ (True ∨ (p4 → p4))))) → p5) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → ((p3 → ((p5 ∧ p5) → (True ∨ p5))) → ((p4 ∧ ((p4 → ((p2 ∨ True) → p2)) ∨ p4)) ∨ (True ∨ (p4 → p4))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62506323687606994621284230484 : ((p3 ∧ (p2 ∧ ((p2 → (((p5 ∨ ((p4 ∨ p2) ∨ (False → p3))) ∨ (((p5 ∨ True) ∧ p1) → p3)) → (False ∨ p2))) → (p1 ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214546904869129880296273738283 : (((False ∨ False) ∧ (p3 ∨ False)) ∨ ((((p2 → p4) ∧ ((p5 ∧ p5) ∧ (((p4 → ((p2 ∨ p1) ∧ p2)) ∧ p2) ∨ (p3 → p3)))) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50982648200066472789246570230 : (((((p4 → True) ∧ p5) → ((p2 ∧ p1) ∧ ((p4 ∨ p3) → (False ∨ ((p2 ∧ False) → p3))))) ∧ (p3 → ((p3 → (p4 ∧ p4)) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115682057394352231891116271732 : (((p5 ∧ (p5 ∧ ((p2 ∨ True) ∧ p3))) ∨ ((p1 ∨ p2) ∨ (p1 ∧ ((False ∧ False) → (((p5 ∨ p1) ∧ (p5 ∨ False)) ∨ p3))))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184755764124619833767029192113 : ((((p4 → p3) → (True ∧ False)) ∧ ((p2 → p2) → (p3 ∧ p3))) ∨ (((p1 → p2) ∧ (True ∧ ((p1 ∧ p2) ∧ (p1 → (p1 ∧ p2))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103028664645844115397794187669 : (((((p3 ∨ p4) ∧ ((True ∨ (True → p1)) ∧ p1)) ∨ ((p5 → p5) ∧ ((p5 ∨ False) ∨ (((p2 ∨ p3) ∧ p2) ∨ True)))) ∨ True) ∧ (False ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111870405646902246789059710389 : (((((((p4 ∧ p4) ∨ True) ∨ p3) ∧ (((False ∧ (p3 → p4)) ∨ p3) ∧ (True ∧ p2))) ∨ (p5 ∧ ((p3 ∧ p3) → p3))) ∨ p2) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136180214673470327440739351384 : (((((p5 → (True ∧ p1)) ∨ p4) → p1) ∧ (((True ∨ ((p1 ∨ p4) ∨ p4)) → ((False → False) → False)) ∨ (False ∧ p5))) ∨ ((p5 ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142482756543233767205299323421 : ((p5 ∧ ((p4 → p2) ∨ (((True ∨ (True → (True → ((p5 → p3) ∧ ((p3 ∨ (p5 ∧ p4)) → False))))) → p3) ∨ True))) → ((p2 → False) ∨ p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742915261224009333785086361089 : ((((p3 → p4) ∨ (((((True → (True ∨ (False → True))) ∨ ((p5 → ((p2 → p3) ∧ True)) ∧ p1)) → ((p1 ∨ True) ∧ p5)) ∨ False) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183857636831651702868177093774 : (((((p3 → (p1 → p1)) ∧ p5) ∧ (p2 ∨ (p5 ∨ True))) ∧ p3) ∨ (((p4 → (((False ∨ p5) → p5) ∧ p3)) → (False ∨ (p1 ∧ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624234956181685586989982408482 : ((((p3 ∨ ((False ∧ (p4 ∧ (p1 ∧ (False → ((((((True ∧ (p5 ∨ p5)) ∧ p2) ∧ p3) ∨ p5) ∧ (False ∧ False)) ∧ p4))))) ∨ p3)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_786519897681253462098581927564 : (((p4 ∨ ((p4 → ((p3 → (p4 ∨ p4)) → ((p3 ∧ False) ∧ (p4 ∧ p1)))) → (((p2 → p4) ∧ p4) → (((p4 ∧ p1) → p3) ∧ p2)))) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : (p3 → (p4 ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h12 := h9 h10
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- False on the left can always be used.
  apply False.elim h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h2.left
  let h16 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h17 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h16
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h18 := h1 h17
  -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
  have h19 : (p3 → (p4 ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h20
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h16
  -- We have shown the premise of h18, we can now drive its conclusion.
  let h21 := h18 h19
  -- We need to get the left conjuct of h21 based on <expert-advice>.
  let h22 := h21.left
  -- We need to get the right conjuct of h22 based on <expert-advice>.
  let h23 := h22.right
  -- False on the left can always be used.
  apply False.elim h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218556572480985952970916378911 : (((False → True) → (p3 ∧ False)) → (p1 → (p2 ∧ (((p3 ∨ (((p5 ∨ p1) → (False ∧ p2)) ∧ True)) ∨ (p2 ∧ (p2 ∧ (p2 ∨ p5)))) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (False → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h10 : (False → True) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h12 := h1 h10
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h17 : (p5 ∨ p1) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h18 := h15 h17
      -- We need to get the left conjuct of h18 based on <expert-advice>.
      let h19 := h18.left
      -- False on the left can always be used.
      apply False.elim h19
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h26 : (False → True) := by
        -- Implications on the right can always be decomposed.
        intro h27
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h28 := h1 h26
      -- We need to get the right conjuct of h28 based on <expert-advice>.
      let h29 := h28.right
      -- False on the left can always be used.
      apply False.elim h29
    case inr h30 =>
      -- One of the premise coincides with the conclusion.
      exact h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622534951405090247215981367113 : ((((p3 ∧ (p5 → (((False ∨ ((p1 → p1) ∧ False)) → (p5 ∧ (False ∨ (p4 ∧ True)))) ∧ ((p4 ∨ ((p4 ∨ p3) ∨ p2)) ∨ True)))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_299379466713464136036216810631 : (False ∨ (((p3 ∧ p2) → ((False → (True ∧ ((p3 ∧ p4) ∧ (p3 ∨ (p4 → (p4 ∧ ((p5 ∨ p2) ∧ (p3 ∨ p2)))))))) → (False ∧ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53987769781461417335164712219 : ((((((True → p2) ∨ True) → ((p2 ∨ p2) ∧ p2)) ∨ False) → (False ∨ (((p4 → False) ∧ (True → ((p4 → p3) → p4))) ∨ (True ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209392554443850229284671626130 : ((p1 → (p1 ∧ ((p2 → p4) → True))) → ((p5 ∧ p3) → ((((p2 → False) ∨ (((((p3 → p2) ∧ p4) ∨ p4) → True) → p1)) ∧ p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174280469746654163997629670591 : (((True ∧ ((p1 ∧ p2) → ((p2 ∧ (p1 → p2)) ∨ p2))) ∧ (p5 → (False ∧ p4))) → ((((p2 → p3) ∧ p1) ∧ p5) ∨ (p5 → (False → p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7



