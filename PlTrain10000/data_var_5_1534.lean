variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313085318671495789242718929221 : (p3 ∨ ((((((False → p5) → p4) ∨ (p2 ∧ p4)) ∨ ((p1 ∨ False) ∨ (((p5 ∨ p5) ∨ (p5 ∨ (True ∨ p3))) ∨ True))) ∨ (p3 ∨ True)) ∨ p4)) := by
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
theorem thm_5_vars_614849709634996974481733813857 : (((((p5 ∨ ((((p4 ∧ p5) → (((p5 ∨ p2) ∨ p2) ∨ False)) → (p5 → (p2 ∨ False))) ∨ False)) ∨ (((p2 ∧ p1) ∨ p3) → True)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136229395167858802600289965453 : (((((True ∧ p5) → p4) ∧ (p3 ∨ p5)) ∨ ((((p1 ∨ p5) ∧ ((p5 ∨ p2) → True)) ∨ (False ∧ p1)) ∨ (p1 → True))) ∨ ((True ∨ False) → False)) := by
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
theorem thm_5_vars_338813512644152804613834529117 : (p1 → ((p2 ∨ p5) ∨ ((p1 ∨ p1) ∧ ((p3 ∧ (True → ((p3 → False) → (((p1 ∧ p5) ∧ p3) → p4)))) → ((p4 ∧ (p4 ∨ p1)) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258301022158048803041721242004 : ((p5 ∨ True) → ((p2 ∧ ((p5 ∨ True) ∨ (p5 ∨ (p1 ∧ ((p2 ∧ p4) ∨ False))))) → (((True ∧ (p1 ∨ ((p2 ∨ p4) → p3))) ∨ p2) ∨ p3))) := by
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
      cases h1
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h22 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h23 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h20
      case inr h24 =>
        -- False on the left can always be used.
        apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204455968467841326466363391650 : ((((p4 ∧ (True ∨ p2)) ∧ False) ∨ p2) ∨ ((p2 → (p1 ∧ (((p3 ∧ ((p4 ∧ p5) ∨ p5)) ∨ (((False ∧ p4) → False) ∨ p2)) → p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165269974652925215199302297166 : ((((((((p5 ∧ p4) → (p3 → (p4 ∧ p4))) ∧ p2) ∨ p4) ∨ False) → p4) → (p2 ∧ True)) ∨ ((p1 → p1) ∨ ((p3 → (p2 ∧ p4)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703496747762702816830090551928 : ((((True → ((False ∨ p3) ∧ (p4 → (True ∨ (True ∨ p2))))) ∨ (((((p1 ∧ p4) ∧ p4) ∧ ((p1 ∨ (p5 → p4)) → p4)) ∧ p3) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352115394256826782921054314858 : (p4 → ((p1 ∧ (False ∧ (p3 ∧ (p1 ∧ p3)))) ∨ (((p3 ∧ False) ∧ (p1 ∨ p4)) → ((p2 ∧ ((p5 ∧ p4) ∨ (p4 → (True ∧ p4)))) ∧ True)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639493982230082594317598025914 : ((((((p1 → p3) ∧ p1) ∧ (((((False → p3) ∨ (p4 ∨ p5)) ∨ True) ∧ ((p3 ∨ p1) ∨ ((p2 → (False ∧ True)) ∨ p2))) ∨ p4)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173374728057685477063948231680 : ((p4 → ((((True ∧ p2) ∧ (False ∨ (p5 ∧ ((p3 ∨ True) ∧ False)))) ∧ p1) ∧ p4)) ∨ (p4 ∨ ((p1 ∨ (p1 ∧ (p5 → p4))) ∨ (False → p4)))) := by
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
theorem thm_5_vars_338356271743882945957617704350 : (p1 → ((((False → True) ∨ p5) → False) ∨ (p4 → ((((p3 ∧ ((p1 → (p5 → (((False ∧ p1) ∧ p5) ∧ True))) ∨ False)) ∨ p2) ∨ p4) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206310703623414802184548901656 : ((p1 ∨ ((p4 ∧ p2) ∨ (p1 ∧ p3))) ∨ (True → ((((((False ∨ p1) ∧ p4) ∨ (p4 → p1)) ∧ p5) ∧ (p1 ∧ p2)) ∨ (True ∨ (p3 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140915419234813495832508208142 : ((((False ∨ False) ∨ (((p2 → (True ∨ p5)) ∧ p3) → False)) ∧ ((p4 ∨ (((p3 ∧ (p3 ∧ False)) ∧ p3) ∨ True)) ∨ p3)) → ((p3 ∨ p3) → False)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
          have h12 : ((p2 → (True ∨ p5)) ∧ p3) := by
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Implications on the right can always be decomposed.
            intro h13
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
            -- One of the premise coincides with the conclusion.
            exact h3
          -- We have shown the premise of h9, we can now drive its conclusion.
          let h14 := h9 h12
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Conjunctions on the left can always be decomposed.
            let h17 := h16.left
            let h18 := h16.right
            -- Conjunctions on the left can always be decomposed.
            let h19 := h17.left
            let h20 := h17.right
            -- Conjunctions on the left can always be decomposed.
            let h21 := h20.left
            let h22 := h20.right
            -- False on the left can always be used.
            apply False.elim h22
          case inr h23 =>
            -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
            have h24 : ((p2 → (True ∨ p5)) ∧ p3) := by
              -- Conjunctions on the right can always be decomposed.
              apply And.intro
              -- Implications on the right can always be decomposed.
              intro h25
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
              -- One of the premise coincides with the conclusion.
              exact h3
            -- We have shown the premise of h9, we can now drive its conclusion.
            let h26 := h9 h24
            -- False on the left can always be used.
            apply False.elim h26
      case inr h27 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h28 : ((p2 → (True ∨ p5)) ∧ p3) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h29
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h27
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h30 := h9 h28
        -- False on the left can always be used.
        apply False.elim h30
  case inr h31 =>
    -- Conjunctions on the left can always be decomposed.
    let h32 := h1.left
    let h33 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h32
    case inl h34 =>
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h35 =>
        -- False on the left can always be used.
        apply False.elim h35
      case inr h36 =>
        -- False on the left can always be used.
        apply False.elim h36
    case inr h37 =>
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h38 =>
        -- Disjunctions on the left can always be decomposed.
        cases h38
        case inl h39 =>
          -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
          have h40 : ((p2 → (True ∨ p5)) ∧ p3) := by
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Implications on the right can always be decomposed.
            intro h41
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
            -- One of the premise coincides with the conclusion.
            exact h31
          -- We have shown the premise of h37, we can now drive its conclusion.
          let h42 := h37 h40
          -- False on the left can always be used.
          apply False.elim h42
        case inr h43 =>
          -- Disjunctions on the left can always be decomposed.
          cases h43
          case inl h44 =>
            -- Conjunctions on the left can always be decomposed.
            let h45 := h44.left
            let h46 := h44.right
            -- Conjunctions on the left can always be decomposed.
            let h47 := h45.left
            let h48 := h45.right
            -- Conjunctions on the left can always be decomposed.
            let h49 := h48.left
            let h50 := h48.right
            -- False on the left can always be used.
            apply False.elim h50
          case inr h51 =>
            -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
            have h52 : ((p2 → (True ∨ p5)) ∧ p3) := by
              -- Conjunctions on the right can always be decomposed.
              apply And.intro
              -- Implications on the right can always be decomposed.
              intro h53
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
              -- One of the premise coincides with the conclusion.
              exact h31
            -- We have shown the premise of h37, we can now drive its conclusion.
            let h54 := h37 h52
            -- False on the left can always be used.
            apply False.elim h54
      case inr h55 =>
        -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
        have h56 : ((p2 → (True ∨ p5)) ∧ p3) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h57
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h55
        -- We have shown the premise of h37, we can now drive its conclusion.
        let h58 := h37 h56
        -- False on the left can always be used.
        apply False.elim h58



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59316600442023247447000171522 : (((p4 ∨ p2) ∨ ((((((p5 → (p3 → (False ∨ p4))) ∧ (p4 ∧ False)) ∨ p5) ∨ (((True ∨ p1) ∧ True) ∨ (p2 → True))) ∨ p3) ∨ p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591436366283696406052662675691 : ((((((p1 ∨ p5) ∨ ((p5 ∨ True) ∨ (p2 ∧ (p4 ∧ (p4 → (p1 ∧ ((p3 ∨ p2) ∧ ((False → p1) → p4)))))))) ∧ (False ∨ p2)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45750218423932897649742056733 : (((False → ((((p3 ∧ (p1 ∧ (((True ∨ p4) ∨ p2) → ((((p2 ∧ p3) → p4) ∨ p2) ∨ False)))) ∧ p5) ∨ False) → (p3 ∧ p1))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58172896905903048427792083247 : (((p3 ∧ p1) ∧ ((False → p2) → ((p1 → p1) → (((p4 ∨ (p4 → (False ∧ (((p1 ∧ p5) → (p5 ∧ p3)) ∧ False)))) → p3) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183481938823772204622767192836 : ((p3 ∨ ((p3 ∨ (p5 ∨ (p5 → p2))) ∨ ((False ∨ False) ∨ True))) ∧ (((True → p5) ∧ False) → (p2 ∧ (((p4 ∧ True) ∧ True) → (p3 ∧ p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h4.left
  let h12 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h1.left
  let h16 := h1.right
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204261245365321383548709376131 : ((((p5 ∧ p4) ∨ (p5 ∨ False)) ∧ False) ∨ (True ∨ (((((p1 → ((((p4 → True) ∧ True) ∨ p2) ∨ p3)) ∨ p4) ∧ p4) ∨ (p2 → p4)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215393866640113975222523694726 : ((p2 ∧ (True ∨ (p1 ∨ p4))) ∨ (((((True → (False ∧ p4)) ∧ (False ∨ ((p2 → p4) → (p3 ∨ p1)))) ∨ True) ∨ (p3 ∨ p3)) ∨ (p3 ∨ p5))) := by
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
theorem thm_5_vars_62775165605651021153749329624 : ((p4 ∧ ((p3 → ((p3 ∨ p5) ∧ (p4 ∨ (True ∧ ((False ∨ p2) ∧ (p2 ∧ (False → ((True ∧ p5) → False)))))))) → (p2 ∨ (p1 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156979312421427886240119891612 : ((((((True ∧ False) ∨ p3) ∨ (p1 ∧ (False → p4))) ∨ (p2 ∨ (p2 ∧ ((p1 → p1) → p3)))) ∨ False) ∨ (True → ((True ∨ p1) ∨ (False ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242575670038425458492014229637 : ((p3 → True) ∧ ((p2 ∧ ((False ∧ p3) → (True ∧ p3))) ∨ (p2 ∨ (((((False ∧ p3) ∨ p5) ∨ p2) ∨ (p4 ∧ True)) → (p1 → (p3 ∨ True)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- False on the left can always be used.
        apply False.elim h7
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206158074475927570973088671521 : ((p5 ∧ ((p4 ∧ (False ∨ False)) ∨ p4)) ∨ (p3 → ((p1 → ((((p3 ∧ p2) ∧ True) ∧ p1) ∨ ((p3 ∨ p3) → ((p5 ∧ p1) → p2)))) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713308963643720041744166475371 : ((((p5 ∨ ((p2 ∨ p3) ∧ (p4 ∨ p5))) ∨ ((False ∨ ((p1 ∧ p2) ∨ (((p5 → p5) ∧ p4) ∨ ((False → False) → False)))) → (True ∨ p5))) ∨ p2) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55989415551535545286743734947 : ((((p1 ∨ (p2 → False)) ∧ p2) ∨ (p4 ∨ ((False → (p1 ∧ p2)) ∧ (((p5 ∨ p1) ∧ (False → ((p4 → False) ∨ (p5 ∧ p1)))) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62210468866881629751506321510 : ((p3 ∧ ((p2 ∧ (((p1 → p4) → (p4 → ((((p4 → p1) → True) ∨ ((p3 ∨ False) → (p5 ∨ True))) ∧ (p1 ∧ p3)))) → p3)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66684028338043914979216177121 : ((True → (((p1 → (False ∧ False)) → p2) → ((p4 ∧ ((False ∨ (p4 → p2)) → (((False ∧ p4) ∧ True) ∧ False))) ∨ (False ∧ (p1 → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214997298952918260110364037743 : (((True ∨ True) → (p4 ∨ p1)) ∨ (p2 → ((p2 ∨ (p4 ∧ ((((True ∧ p5) → False) → p4) → p5))) ∧ ((True → (p4 ∧ (p3 ∧ False))) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141017030691055332749017689030 : (((((((p4 ∨ p1) ∧ p3) ∨ p2) ∨ p1) → False) ∧ ((p2 ∨ (False ∨ (True → (p3 ∧ ((p4 → p2) ∨ p1))))) ∧ p2)) → (p3 ∧ (False ∧ p3))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : ((((p4 ∨ p1) ∧ p3) ∨ p2) ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : ((((p4 ∨ p1) ∧ p3) ∨ p2) ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h12
      -- False on the left can always be used.
      apply False.elim h13
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h15.left
  let h17 := h15.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h18 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h19 : ((((p4 ∨ p1) ∧ p3) ∨ p2) ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h20 := h14 h19
    -- False on the left can always be used.
    apply False.elim h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h24 : ((((p4 ∨ p1) ∧ p3) ∨ p2) ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h25 := h14 h24
      -- False on the left can always be used.
      apply False.elim h25
  -- Conjunctions on the left can always be decomposed.
  let h26 := h1.left
  let h27 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h28 := h27.left
  let h29 := h27.right
  -- Disjunctions on the left can always be decomposed.
  cases h28
  case inl h30 =>
    -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
    have h31 : ((((p4 ∨ p1) ∧ p3) ∨ p2) ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h29
    -- We have shown the premise of h26, we can now drive its conclusion.
    let h32 := h26 h31
    -- False on the left can always be used.
    apply False.elim h32
  case inr h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h34 =>
      -- False on the left can always be used.
      apply False.elim h34
    case inr h35 =>
      -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
      have h36 : ((((p4 ∨ p1) ∧ p3) ∨ p2) ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h29
      -- We have shown the premise of h26, we can now drive its conclusion.
      let h37 := h26 h36
      -- False on the left can always be used.
      apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344180950785292496631029505986 : (p2 → (p1 ∨ ((p1 ∨ (((p5 ∨ (p3 ∧ p5)) ∧ ((p1 → p3) ∧ (p3 ∧ ((p1 ∧ (p1 ∧ p2)) ∧ p4)))) ∧ p4)) ∨ ((p2 ∧ False) → p5)))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641989142862363584398562808440 : (((((p5 → p5) → (p3 ∨ (False → ((True → p2) ∨ (False ∨ (((True → p4) ∨ True) ∧ ((p1 → ((p1 ∨ p4) ∧ True)) ∧ p3))))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714828324110575755604831538623 : ((((p2 ∧ ((p3 ∧ p1) ∧ (p3 ∨ p3))) → ((False → p3) ∧ ((p2 ∧ False) ∨ (((False ∨ p4) ∨ ((p5 ∨ (p3 ∧ p1)) → False)) → p4)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h14 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h15 : (p5 ∨ (p3 ∧ p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h9
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h16 := h14 h15
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- One of the premise coincides with the conclusion.
        exact h21
    case inr h22 =>
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h23 : (p5 ∨ (p3 ∧ p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h17
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h24 := h22 h23
      -- False on the left can always be used.
      apply False.elim h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38688502097299353071200145956 : ((((p5 → ((p2 → (p5 ∧ p1)) ∧ p4)) ∧ ((((p2 ∨ p5) ∧ p3) ∧ (p4 ∨ (p5 ∧ (((True ∧ p3) → False) ∨ False)))) ∨ p5)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317861925710595615603527766670 : (p4 ∨ (((p5 ∧ p5) ∨ (((p4 → p3) → (False → p2)) → ((p1 ∨ (p4 ∧ ((p4 → (p4 ∧ p1)) → (p4 ∨ p3)))) ∨ (p4 → True)))) ∨ p1)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154768947161902849288963530535 : (((p1 ∨ (p2 → (((p3 ∧ False) ∨ ((p4 ∧ (False → p2)) → True)) ∨ (p2 → p1)))) ∨ (p3 ∨ p1)) ∧ (True → ((p5 ∧ (True ∧ p2)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266201701857993919478343041509 : (True ∧ (p4 → (((p1 → p5) → (((True ∧ p5) ∨ p2) ∧ (((p4 ∧ p2) → p1) → p5))) ∨ (p2 → ((True ∧ False) → ((p1 → p4) → True)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_217179505784842031576090947670 : ((((p5 ∧ False) → p4) ∨ False) → (True ∧ (((p4 ∨ ((p2 → (p1 → p3)) ∨ (False ∨ True))) ∨ (True ∧ False)) ∧ ((p1 → (p4 → p1)) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_128616405845031971942469312375 : (((((p1 → (((p3 ∧ p1) ∧ p1) → (False ∧ False))) → (p5 ∧ (p2 ∨ ((p3 ∧ p5) ∧ (False ∨ p2))))) ∨ True) ∧ True) ∧ (False → (False → p1))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343254333900553055621733873116 : (p2 → ((p4 → (True ∨ p4)) → ((False ∨ ((p3 ∧ (((False ∨ p3) ∨ p5) ∧ False)) ∨ True)) → (True ∧ ((p3 → ((False ∨ False) ∧ False)) ∨ True))))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- False on the left can always be used.
          apply False.elim h10
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618146392364733017395003648247 : (((((p3 ∨ ((p1 → False) ∧ False)) ∧ (p4 → (((p5 ∨ p5) ∧ ((p3 ∨ (p2 → (p4 ∨ ((p3 → p2) ∨ True)))) → False)) ∨ p1))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_115186427607523040191936054164 : ((((((p2 ∧ p4) ∧ True) ∨ p4) ∧ ((p1 → p3) → p3)) ∧ (((False → ((False → p4) ∧ True)) ∧ True) ∧ (p2 → (False → p2)))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40835058394527406603385559656 : ((((p2 → (((((p3 → p5) ∨ p3) ∨ (True ∨ p3)) → (((True → p4) ∨ (p1 ∧ True)) ∧ p1)) → ((p3 → p4) → p4))) → p2) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806094810580075599095951367118 : (((p4 → ((p1 ∨ ((p5 ∧ ((((p4 → True) → ((False ∧ (True ∨ (True → (False → (p5 ∧ True))))) ∧ p3)) ∨ p3) ∨ p2)) ∨ p3)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136143214113893267391822783067 : (((((True ∨ (p3 ∨ p2)) ∧ True) ∨ (True → p3)) → (((p5 ∨ p3) ∨ (p3 ∨ True)) ∨ (False ∨ (False → (p3 ∧ p5))))) ∨ (False → (p3 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309256733458841159099227059549 : (p2 ∨ (((p2 ∧ p2) ∨ (((p5 → ((p4 ∨ p4) ∨ p3)) → (((p3 ∧ (p2 ∨ p3)) ∨ p5) → p4)) ∨ ((p5 ∨ p5) → p5))) ∧ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618260511282072900510224792599 : ((((((True ∧ (p5 ∨ p2)) → p3) ∨ (p4 → (((((p3 → ((p1 ∨ p4) ∧ p4)) → p1) ∧ (p2 ∨ False)) ∨ p4) ∨ (True ∧ True)))) ∨ False) ∨ p4) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241455300307732438287539533028 : ((False → p2) ∧ (((p3 → ((p5 ∨ True) → ((p2 ∧ (((p3 ∧ (False ∧ (p4 ∧ p4))) ∧ p2) ∧ p5)) ∨ (p3 ∨ (p4 ∧ p1))))) ∨ p2) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309797481257123337006821267197 : (p2 ∨ ((((((p2 → (p5 ∨ (False → p2))) → (True ∧ p3)) → False) ∨ p3) → (p5 ∨ (p5 ∨ (True ∨ p5)))) ∨ (p1 ∨ ((True ∨ p2) ∨ p4)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179090458565419808812673817678 : ((False ∧ ((((p3 → False) ∧ ((True ∨ True) ∧ (p5 ∧ False))) ∧ p2) ∨ p4)) ∨ (((p3 → False) ∨ p4) → (p4 → (p1 → (p5 ∨ (p2 → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252066614324088462079390952379 : ((p4 → p1) ∨ (False ∨ (p5 ∨ (((p4 ∧ (p3 → (((False ∨ (True ∧ (p2 → (p3 ∨ p5)))) ∨ p1) ∧ (True ∧ (p4 → p3))))) ∧ p5) ∨ True)))) := by
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
theorem thm_5_vars_785883270710119343503788629051 : (((p4 ∨ (((((p4 ∨ p4) ∨ (((True ∧ (p5 ∨ p5)) → ((p4 ∧ p5) → (p2 ∨ p5))) ∧ p1)) ∨ p1) ∨ (p1 ∨ p5)) ∧ (p2 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198568648559942049103670969076 : ((p1 ∨ (((False ∧ True) → p5) → (p3 ∧ p4))) ∨ ((p1 ∨ ((p3 ∧ ((((True → (False ∨ (p1 ∨ p1))) ∧ True) ∧ False) → False)) ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346334093628356170524124959259 : (p3 → ((((p2 ∧ (((p5 ∧ p2) → (p5 ∨ p3)) ∧ p5)) → ((False ∨ p4) ∧ p2)) → ((p3 → p5) → (p2 ∨ (p5 → False)))) ∨ (p4 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135087951304497682356077102891 : (((((p4 ∧ (((True ∨ p4) ∧ p1) → p1)) → (p4 ∧ (True ∧ p4))) → ((p2 ∨ p3) ∧ (False ∧ False))) ∨ (p4 → p3)) ∨ (p5 ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42553508216617015229081590598 : (((p1 ∨ (True ∧ (((p2 ∨ (False ∧ p1)) ∧ ((((True → (p5 → (p3 ∨ (p5 ∨ p5)))) → p1) ∨ p3) ∨ (p5 ∨ p4))) ∨ p1))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116448898352288994518630625049 : (((p5 → (p5 → p2)) → ((((p2 ∨ (p1 → p4)) ∨ False) ∨ p4) ∧ ((p4 ∨ p3) ∨ ((False → True) ∨ (False ∧ (False → p5)))))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611348224062796397881174157876 : ((((((False → p3) → (((p1 → ((((p3 ∨ p4) → p1) ∧ (p5 ∧ (p4 ∧ p3))) → True)) ∧ ((True ∧ p2) ∧ p1)) ∧ p1)) → p2) ∨ p2) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60098218012567944505136051405 : (((p3 ∨ p1) → ((((((p4 → p3) → p1) ∧ True) ∧ ((((p5 ∨ (True ∨ p1)) ∨ p4) ∧ ((p3 ∧ p2) → p5)) ∨ True)) ∨ True) ∨ p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218550611292988147452799285621 : (((True → p2) → (False ∨ p4)) → ((((((True ∧ (p5 ∧ p5)) ∨ (p5 ∧ ((p4 ∨ p2) ∧ p1))) ∧ p2) → p1) ∧ p4) ∨ (True ∨ (p4 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227855783691688433469401498180 : ((p2 ∧ (p1 ∨ True)) ∨ ((False ∨ (p4 ∧ (p4 → p2))) ∨ ((((p1 → p2) ∧ ((True ∨ True) ∧ (False ∨ (p5 → (False ∨ True))))) → p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710444446605373656818998746971 : ((((((False → True) → (True ∧ p1)) → p4) ∧ (((p2 → p5) ∨ p3) ∧ (((True → False) ∧ (((p4 → (True ∨ p3)) → p4) ∧ p1)) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227503359028670887370388842722 : ((True ∧ (p1 ∨ p1)) ∨ (p2 ∨ ((True ∧ p3) → ((p2 ∧ (((p5 ∨ p1) → (p1 → ((p2 ∧ p4) ∧ (True → p5)))) ∨ p4)) → (False ∨ p3))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111721078628244643522556822860 : (((((p2 ∧ (False ∨ (p4 ∨ p2))) ∨ ((((p5 → (False ∨ p3)) ∨ p5) → ((p1 ∨ p5) → p4)) ∨ (p2 ∨ False))) → p1) ∨ True) ∨ (p5 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47033052222727874936214321309 : (((((p4 ∨ (((False ∨ p1) → ((p5 ∨ False) ∨ ((((p2 → True) ∨ p5) ∨ True) ∧ p5))) ∧ p3)) ∧ p5) ∧ (p3 ∧ False)) ∨ (p2 → p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327837069479912473650784230389 : (True → (((((p1 ∨ p1) ∨ (((p3 → (False ∨ ((p5 ∨ p5) ∨ True))) → p5) ∧ p2)) → p3) ∨ (p1 ∧ (p1 ∨ (p4 ∧ p3)))) ∨ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190661316941419534959092881380 : (((p5 ∨ (p1 ∨ ((p4 ∧ (False ∨ p5)) ∨ p3))) → p3) ∨ (True → ((True ∧ p3) → (True → ((p4 ∨ ((p4 → False) ∨ (False → p3))) ∨ p3))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805751593540952656609413485636 : (((p3 → (p3 → ((p4 ∨ (True ∧ ((((((((p2 ∨ (False → p5)) ∨ p5) ∨ p4) ∧ p2) ∧ False) → p4) → False) ∧ (True ∧ p2)))) ∨ True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41913361841196092855235788166 : (((((False ∨ p4) → p3) → ((True ∧ ((False → p4) ∧ (p5 ∧ False))) ∧ (False ∧ (False → ((p4 ∧ (p4 → p3)) ∧ (p5 ∨ p3)))))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791067640022863342516876809506 : (((True → (((p5 ∨ ((p5 → ((p3 ∧ p3) ∧ (((p3 ∨ True) → False) ∨ p3))) → ((p1 ∨ False) ∨ (p2 ∧ p2)))) ∧ (p1 → p2)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779319656907792886248369338024 : (((p2 ∨ ((p2 ∨ (p4 → ((((p2 ∧ p5) ∨ (((((((p5 → p4) → False) ∧ p1) ∧ p4) ∨ p2) ∨ p2) ∨ p2)) → p4) → p1))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189687757621999523710077587857 : ((p3 ∨ ((p4 ∨ ((p3 ∧ p2) ∨ (p5 ∧ p4))) ∨ True)) ∧ (((False ∧ p3) ∨ (((False ∨ p4) → ((False ∧ True) → (p3 ∧ p2))) ∨ p1)) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53888042385877765248989819811 : (((True ∧ ((((p2 ∨ p4) ∨ True) ∧ p5) ∧ (p4 → p5))) ∨ (p4 → (((False ∧ ((p1 ∨ (p3 → (p2 → False))) ∨ p3)) ∧ p3) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683472374107881927551927243663 : ((((p2 → (p1 ∧ (p3 ∧ (False ∨ (p2 → (p1 ∨ ((False ∧ (True ∨ (False ∧ p4))) ∨ p2))))))) ∧ (p5 ∨ (((p4 ∧ p3) ∨ p3) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345484001765120999207050166757 : (p3 → (((((False → False) ∨ p4) ∧ ((p2 ∨ ((p2 ∧ p2) ∨ p1)) ∨ ((p5 ∨ (True ∨ p5)) ∧ p1))) ∧ ((p3 → p5) ∨ (p2 ∧ False))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263069063968523752402431021368 : (True ∧ ((((((True → (p4 ∨ (((p2 → p4) ∧ (p2 ∧ (True ∨ p2))) → True))) → p2) ∨ True) ∧ (p1 → (p4 ∨ True))) ∧ p2) ∨ (p2 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322522712854155517699866841691 : (p5 ∨ ((p2 ∧ (((((True → True) ∧ p2) ∨ ((((p4 ∧ p1) ∧ True) → p1) → p3)) → p5) ∧ (((False ∧ (True ∨ False)) ∨ False) ∨ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158565199302058099400049500733 : ((True ∧ (((p4 ∧ (p3 → p5)) → ((p5 → False) ∧ ((p1 → (p3 → True)) → True))) ∧ (p2 ∧ False))) ∨ (p5 → (((False ∨ True) ∨ p2) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159391168298727353618356982869 : (((((False ∨ ((p1 ∧ (p2 ∧ (((p3 → True) ∧ p4) ∧ (True ∨ p5)))) → p1)) ∧ True) → p3) ∧ p5) → ((True ∧ p3) ∨ (False ∨ (p1 → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∨ ((p1 ∧ (p2 ∧ (((p3 → True) ∧ p4) ∧ (True ∨ p5)))) → p1)) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h16 := h2 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172607457524119676525060113284 : (((p4 ∨ (True ∨ True)) → ((False ∨ False) ∨ (p2 → (True → ((True ∨ p5) ∧ True))))) ∨ (((((False ∨ (p4 → p3)) ∧ False) ∧ True) → p2) → p1)) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702284277684207694883931428709 : (((((p3 ∧ ((p3 ∧ (p5 → (p5 ∧ False))) ∨ p5)) ∧ False) ∨ ((p4 → ((p1 ∨ p2) ∨ p4)) ∨ ((((p5 ∧ p3) ∧ p1) → p3) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180192829886439092320079280883 : ((((p2 ∧ (p5 ∧ True)) ∧ ((p2 ∨ True) → (True ∨ (p5 ∧ True)))) → p4) → (((p2 ∨ p3) ∧ p4) ∨ ((False → ((True → False) ∨ True)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174016580040253961096286468401 : (((p3 ∧ (p4 → (p1 ∨ ((True ∨ (((False → p1) → p1) → True)) → p5)))) → True) → (((p1 → (p1 → p5)) ∧ (p1 ∨ (p5 ∧ p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53967552781934928262209620982 : (((((False → p4) ∨ (p2 ∨ (p3 ∧ (p4 ∨ p1)))) ∧ p2) → (((p4 → ((p5 ∨ p3) ∧ p2)) → p4) ∨ (p4 ∨ (p2 ∧ (True ∨ True))))) ∨ p3) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h3
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h3
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157889583644486574517330377674 : (((False ∨ (((False ∧ False) ∧ p3) ∧ ((p5 → p2) ∧ p1))) ∨ (True → ((p2 ∨ (False ∨ p1)) ∨ p5))) ∨ ((False ∧ (p2 → p4)) → (p2 ∧ p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150421438737531178475220108640 : ((((((False → p2) → (p5 ∧ p1)) → ((((p4 → False) ∧ ((p3 → p4) ∧ p3)) ∧ p3) ∧ p4)) ∨ p5) ∧ p5) → (((p1 ∧ True) ∨ True) ∨ p3)) := by
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
theorem thm_5_vars_65319368297646329178449922167 : ((p3 ∨ ((p1 → ((((p2 ∧ (((p1 ∨ False) → p5) ∨ ((False ∨ p3) ∧ p4))) ∨ (p3 ∨ True)) ∨ p5) ∨ p2)) ∨ (p3 ∧ (p5 → p5)))) ∨ p4) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207931894463627838361591070659 : (((p3 ∨ (False → p4)) ∧ (True → True)) → ((((False → p3) ∧ p4) ∧ ((True → ((p4 → (((True ∧ True) ∧ True) → False)) ∨ True)) ∨ p1)) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134242580094541977622811687432 : (((((p3 ∨ (p3 ∨ p4)) → p1) → ((((p2 → ((p3 → p4) ∧ p1)) ∨ p3) → ((p2 → p5) ∨ p2)) ∧ p5)) ∨ p3) ∨ (True ∨ (p2 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631220569593305588812254692276 : ((((((((((p5 → p5) ∧ p4) → (p5 ∧ ((p1 ∨ True) → (False → True)))) ∧ ((False ∨ p4) → p1)) ∨ (p4 ∨ p4)) → False) → p1) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232017662051497632474717061725 : (((p3 ∨ True) → False) → (((p4 ∨ True) ∨ (p2 ∨ (p1 → p3))) ∧ ((p1 → (False ∨ p1)) → (((p5 ∨ (p3 → p3)) → (p1 → False)) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : (p3 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : (p3 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h9
    -- False on the left can always be used.
    apply False.elim h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600922702744559642003735362205 : ((((p1 ∧ (((False → p4) ∧ (((True ∧ p3) ∨ False) ∧ ((p5 ∨ (((p4 → (p2 → True)) → (p2 → p2)) ∧ p3)) ∧ p3))) ∨ False)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352051570760879697319833090933 : (p4 → ((p4 → ((False ∧ True) ∨ (False → (False ∨ p1)))) → ((((False ∧ (p1 ∧ ((p2 ∨ (False ∨ False)) → p1))) ∧ True) ∧ p5) ∨ (p3 ∨ True)))) := by
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
theorem thm_5_vars_39673315082314916786149892249 : (((p4 ∨ (((p3 → (p3 → p2)) ∧ (p4 ∧ ((p4 ∨ ((p1 ∧ p1) ∧ (((True → p3) → (p1 → False)) → p4))) ∨ True))) ∨ True)) ∧ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_321681607691559520836820879908 : (p4 ∨ (p4 → ((((p5 ∧ (False ∧ p1)) ∨ p4) ∨ (p1 ∧ p1)) ∧ ((p1 → ((p3 → p5) ∨ (p5 → (False ∨ p5)))) ∨ (p1 ∧ (p5 ∧ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197666013677646803372762310234 : ((((p4 → False) ∨ (p5 ∧ p5)) → (p1 ∧ p1)) ∨ (((p3 ∨ True) → False) → ((p5 ∧ ((p1 → (p4 ∨ (p3 ∧ (p2 ∨ p5)))) → p5)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213186647024541273853556864702 : ((((p3 ∨ p1) ∨ p4) ∧ p1) ∨ (((((p4 ∨ False) → p1) ∨ True) ∧ (True → (p1 ∧ ((((p4 ∧ p2) ∨ (p4 ∧ p3)) → False) ∨ p3)))) → p1)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148313718408830081749180726936 : (((p5 ∧ ((True ∨ p2) ∧ ((p4 → ((True ∧ p1) → (p2 ∧ False))) ∨ (p1 ∨ False)))) → (p4 → (False ∧ False))) ∨ (((False ∨ p3) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238197597625421021988875542618 : ((True ∨ p4) ∧ (((p4 → (p1 ∨ (((False ∧ p5) ∨ p1) ∧ p2))) ∧ ((False ∧ p4) ∨ True)) ∨ (p2 → (p4 → ((p3 → (p2 → p4)) ∨ p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



