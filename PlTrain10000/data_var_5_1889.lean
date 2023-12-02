variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137334580317814033765132068083 : ((p2 ∧ (False ∨ (p2 ∨ (p4 ∨ ((((True ∧ True) → True) → (False ∨ True)) → ((p1 → p1) → ((p4 → True) ∧ p3))))))) ∨ (True ∨ (p1 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2188134293175687875057356272 : ((((p1 ∨ ((p4 ∨ True) ∨ p1)) → ((p5 ∧ p4) ∧ True)) → (p5 ∧ (p4 ∨ p4))) ∨ ((False ∧ (p3 → ((p3 ∨ p3) ∧ p3))) ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ ((p4 ∨ True) ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p1 ∨ ((p4 ∨ True) ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49084242664740484048603489321 : (((((((((p3 → (p2 → True)) ∧ True) ∨ False) ∨ (p4 ∨ (True → p1))) → p5) ∧ True) ∧ ((p1 ∧ p1) ∧ p3)) ∨ ((p2 ∧ True) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138743432280250559445776983273 : (((((True → False) ∧ p3) ∧ (False ∨ (((p2 ∨ p5) ∨ p5) ∧ ((p1 ∧ p4) ∨ ((p3 → (False → p3)) ∧ True))))) ∧ p5) → (p5 → (False ∧ p4))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h18 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h19 := h7 h18
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h23 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h24 := h7 h23
          -- False on the left can always be used.
          apply False.elim h24
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h26 =>
          -- Conjunctions on the left can always be decomposed.
          let h27 := h26.left
          let h28 := h26.right
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h29 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h30 := h7 h29
          -- False on the left can always be used.
          apply False.elim h30
        case inr h31 =>
          -- Conjunctions on the left can always be decomposed.
          let h32 := h31.left
          let h33 := h31.right
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h34 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h35 := h7 h34
          -- False on the left can always be used.
          apply False.elim h35
    case inr h36 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h37 =>
        -- Conjunctions on the left can always be decomposed.
        let h38 := h37.left
        let h39 := h37.right
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h40 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h41 := h7 h40
        -- False on the left can always be used.
        apply False.elim h41
      case inr h42 =>
        -- Conjunctions on the left can always be decomposed.
        let h43 := h42.left
        let h44 := h42.right
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h45 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h46 := h7 h45
        -- False on the left can always be used.
        apply False.elim h46
  -- Conjunctions on the left can always be decomposed.
  let h47 := h1.left
  let h48 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h49 := h47.left
  let h50 := h47.right
  -- Conjunctions on the left can always be decomposed.
  let h51 := h49.left
  let h52 := h49.right
  -- Disjunctions on the left can always be decomposed.
  cases h50
  case inl h53 =>
    -- False on the left can always be used.
    apply False.elim h53
  case inr h54 =>
    -- Conjunctions on the left can always be decomposed.
    let h55 := h54.left
    let h56 := h54.right
    -- Disjunctions on the left can always be decomposed.
    cases h55
    case inl h57 =>
      -- Disjunctions on the left can always be decomposed.
      cases h57
      case inl h58 =>
        -- Disjunctions on the left can always be decomposed.
        cases h56
        case inl h59 =>
          -- Conjunctions on the left can always be decomposed.
          let h60 := h59.left
          let h61 := h59.right
          -- One of the premise coincides with the conclusion.
          exact h61
        case inr h62 =>
          -- Conjunctions on the left can always be decomposed.
          let h63 := h62.left
          let h64 := h62.right
          -- We want to use the implication h51 based on <expert-advice>. So we show its premise.
          have h65 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h51, we can now drive its conclusion.
          let h66 := h51 h65
          -- False on the left can always be used.
          apply False.elim h66
      case inr h67 =>
        -- Disjunctions on the left can always be decomposed.
        cases h56
        case inl h68 =>
          -- Conjunctions on the left can always be decomposed.
          let h69 := h68.left
          let h70 := h68.right
          -- One of the premise coincides with the conclusion.
          exact h70
        case inr h71 =>
          -- Conjunctions on the left can always be decomposed.
          let h72 := h71.left
          let h73 := h71.right
          -- We want to use the implication h51 based on <expert-advice>. So we show its premise.
          have h74 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h51, we can now drive its conclusion.
          let h75 := h51 h74
          -- False on the left can always be used.
          apply False.elim h75
    case inr h76 =>
      -- Disjunctions on the left can always be decomposed.
      cases h56
      case inl h77 =>
        -- Conjunctions on the left can always be decomposed.
        let h78 := h77.left
        let h79 := h77.right
        -- One of the premise coincides with the conclusion.
        exact h79
      case inr h80 =>
        -- Conjunctions on the left can always be decomposed.
        let h81 := h80.left
        let h82 := h80.right
        -- We want to use the implication h51 based on <expert-advice>. So we show its premise.
        have h83 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h51, we can now drive its conclusion.
        let h84 := h51 h83
        -- False on the left can always be used.
        apply False.elim h84



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655466705969008065361952381456 : (((((p3 ∨ (((p3 ∧ p4) ∧ (((p4 ∨ False) ∨ (p2 ∧ (p1 ∧ (p5 ∨ p3)))) ∨ (p1 ∨ True))) ∧ p3)) ∨ (p4 ∧ True)) ∨ (p2 → p2)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_324679206523693734661942683445 : (p5 ∨ ((False ∨ (True → p2)) ∨ (p5 → ((p4 → (((p2 → p5) → p1) → (p5 ∧ ((p5 ∧ (p4 → False)) ∨ (True ∨ (p1 ∨ True)))))) ∨ True)))) := by
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
theorem thm_5_vars_58515852081825906389098003541 : (((p5 ∨ True) ∧ ((True ∨ p4) → ((((p3 ∨ (False ∨ (False ∧ True))) → ((((p5 → False) → p5) → p3) ∨ (p4 ∧ p1))) → p5) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321016311927484147557693859852 : (p4 ∨ (False ∨ ((p5 → ((p2 ∧ p1) ∧ (True → p3))) → (p2 ∨ (p3 ∨ ((False ∨ ((False ∧ p4) → p3)) ∨ (p1 → (False ∧ (p5 ∨ p4))))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_327181375794975578300934926241 : (True → ((p1 ∨ (p2 ∧ (p5 → ((((p3 → p2) ∧ (True ∨ True)) ∧ ((p1 ∨ p4) → ((p2 ∨ ((p5 ∨ p5) ∧ p1)) ∧ True))) ∧ p4)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111903333754644866944510248061 : (((((False ∧ p1) ∨ (p3 ∨ (p4 → (p2 ∨ ((p2 → p2) ∨ (p2 ∧ p5)))))) → ((((p2 ∧ p5) ∨ p2) ∨ False) → p5)) ∨ p5) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612131085691849673055170145907 : (((((((p3 ∨ ((((p3 → (p5 ∧ p5)) ∧ p1) → p3) → False)) ∧ (True ∧ p3)) ∨ ((False → (p4 → p4)) ∨ False)) ∧ (p4 ∨ p5)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56742740026675655019298223384 : ((((True → p4) ∨ True) ∧ (((p3 ∨ (((p2 ∨ (p4 ∨ p4)) → ((False ∧ p2) → False)) ∧ p5)) ∨ (p1 ∧ (False ∨ False))) → (p4 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_902515353053516945215063935708 : (((((True → ((p3 ∨ p1) → ((False ∧ p5) ∧ p5))) ∧ ((((p4 ∧ False) → (p3 → p4)) → False) → True)) ∧ (((True ∧ p3) ∧ p5) ∨ p3)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h11 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h12
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : (p3 ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- One of the premise coincides with the conclusion.
    exact h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65639142703684332625920229565 : ((p4 ∨ (((p1 ∧ (False → (p4 ∨ (p5 ∧ (((False ∨ False) ∨ True) ∧ p4))))) ∧ ((((p2 ∧ p5) → p1) ∨ (False ∧ p2)) ∨ p1)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324757432075337469413702926358 : (p5 ∨ ((p1 → (True ∨ p5)) → (((p3 ∧ (p2 ∨ (((p3 ∨ False) ∨ p4) ∨ p5))) ∧ False) ∨ (False → ((False → (False → False)) ∨ (True ∨ p5)))))) := by
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
theorem thm_5_vars_347848098977115662213804017872 : (p3 → ((True ∧ (p1 → False)) → (((False ∧ (False ∧ p3)) → p4) → (True ∧ ((p4 → ((False ∧ (p4 ∧ p4)) ∨ True)) → ((True → p5) → p5)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45058925905275354995448345638 : ((((p3 → True) ∨ (p3 → (False ∨ ((p1 ∧ p5) → (((((p5 ∧ (p3 ∧ p2)) ∧ False) ∧ (p5 → (p5 ∧ p1))) → p1) ∧ False))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213336995246231238185336510999 : (((p2 ∧ (p1 ∨ False)) ∧ p3) ∨ (((False ∧ ((((False ∨ (True ∨ p2)) ∧ p1) → (p3 ∧ False)) ∨ True)) ∨ p3) → (p4 ∨ ((p3 ∨ p4) → True)))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165763909167238595059831103671 : (((((False → True) → p2) ∧ p3) → ((p5 ∨ p4) ∨ (p5 ∧ (True ∧ ((p2 → p1) ∨ p1))))) ∨ (((False → p1) → ((True → p5) ∨ False)) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122206827120042652264066578403 : (((((p5 → (p2 → ((p5 ∧ p1) ∨ p5))) → (p2 ∧ (p2 ∧ p5))) ∧ (False → (p2 → ((p5 → False) ∧ True)))) ∧ (p5 → p1)) → (p2 ∧ p5)) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p5 → (p2 → ((p5 ∧ p1) ∨ p5))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h6
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- One of the premise coincides with the conclusion.
  exact h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h15 : (p5 → (p2 → ((p5 ∧ p1) ∨ p5))) := by
    -- Implications on the right can always be decomposed.
    intro h16
    -- Implications on the right can always be decomposed.
    intro h17
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h16
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h18 := h13 h15
  -- We need to get the right conjuct of h18 based on <expert-advice>.
  let h19 := h18.right
  -- We need to get the right conjuct of h19 based on <expert-advice>.
  let h20 := h19.right
  -- One of the premise coincides with the conclusion.
  exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353836679943814874813742198290 : (p4 → (p1 → ((((((p1 ∨ p5) → (((p5 ∧ ((p4 ∧ p5) ∨ True)) ∨ p5) ∧ p4)) → False) ∨ (p4 ∧ p3)) ∨ ((False ∧ p4) → p1)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55710023972087639107146409524 : ((((p5 ∨ (False → True)) ∨ p3) ∧ ((True → False) → ((p4 ∧ ((p2 ∨ (p2 ∧ (((p3 ∧ p2) → p3) ∨ p1))) ∧ p3)) ∨ (p4 → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791963016935059436911243512090 : (((True → ((p4 → ((((True → p5) → (p3 ∧ ((((p1 → p5) → (p2 ∨ p4)) ∨ p2) ∧ p3))) ∧ (p1 → True)) → False)) ∨ (p1 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180862674909741347098454270119 : (((p5 ∧ (True ∨ p1)) ∨ (p1 ∨ (p3 → (True ∨ ((False ∨ True) ∧ p4))))) → ((True → ((p5 ∧ (False → (p1 ∧ p3))) ∧ p1)) ∨ (p4 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602113181083983231959299267866 : ((((p5 ∧ ((((p4 → p4) ∨ ((p3 ∧ (p5 ∨ False)) → True)) → (p3 → p1)) ∨ ((False → (p1 ∧ False)) ∧ (p2 ∨ (p3 ∧ p2))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207105667514949704487475384808 : (((p1 ∨ (p2 ∨ (p3 ∧ p5))) ∧ p5) → (((p4 → True) ∧ p3) ∨ ((((False ∧ ((p4 → p2) → p4)) ∧ p3) ∨ ((p3 ∨ p1) ∨ True)) ∨ p2))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
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
theorem thm_5_vars_347426783319083563735171813726 : (p3 → ((p1 → (((False → p3) ∧ (True ∧ True)) ∨ p1)) → (((p5 → (p2 ∨ p2)) → (p1 ∧ ((p1 ∨ p3) ∨ ((p4 ∧ p1) → p3)))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134229842987800432761034265295 : ((((p3 → (p2 ∨ ((p5 → p5) ∧ True))) → ((p3 → True) → ((p4 ∧ ((p4 ∨ p1) → (p3 ∨ True))) → False))) ∨ True) ∨ ((p3 ∨ p1) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263078129579250314167275348717 : (True ∧ ((((p5 → ((False → (p2 ∧ p4)) ∧ (p2 ∨ (False ∧ ((((False → False) ∧ p2) → (True ∨ p1)) ∧ p3))))) ∨ True) ∨ p4) ∨ (True ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133446733202755528481928544871 : ((p5 → ((((False ∨ ((((p4 → True) ∨ p4) → False) ∧ p2)) ∧ p3) ∨ ((p5 ∨ (p3 ∨ (p2 ∧ p4))) ∨ p3)) ∧ True)) ∧ (True ∨ (p5 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622848388076520782764373837359 : ((((p5 ∧ (((((False ∨ ((True → p1) → (p2 ∧ p2))) → (p1 ∨ ((False ∧ False) ∧ p3))) ∧ p4) → ((p1 → p3) → False)) ∨ p5)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259453489478740526359435525668 : ((False → p4) → (((((True ∧ p5) ∧ False) ∧ p4) ∨ ((p4 ∨ (p5 → (p5 → p5))) → p5)) → (p2 ∨ ((((p3 ∨ p5) ∨ p5) → True) → p5)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h12 : (p4 ∨ (p5 → (p5 → p5))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h15 := h10 h12
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_871106579960213120025978150472 : ((((p1 ∨ ((((p2 → ((p2 ∧ p4) → p4)) ∨ ((p5 ∨ p3) ∧ (((p1 → p5) ∨ False) → p5))) ∨ p1) → ((False ∧ p2) ∨ True))) → p3) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ ((((p2 → ((p2 ∧ p4) → p4)) ∨ ((p5 ∨ p3) ∧ (((p1 → p5) ∨ False) → p5))) ∨ p1) → ((False ∧ p2) ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h9 =>
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152613358582492498905771568144 : (((p5 ∧ p5) ∧ (((((True ∨ (p3 ∧ (True → p2))) ∧ p3) ∨ ((p5 ∧ True) ∧ p1)) ∨ (True → p3)) ∧ True)) → (p1 ∨ (True → (p1 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
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
        -- Implications on the right can always be decomposed.
        intro h13
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h20
  case inr h23 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h24
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51187390678691241109561879834 : (((((((p5 ∧ False) ∧ (((False ∧ p2) ∨ p4) ∨ p2)) ∧ p4) ∨ False) ∨ ((p5 ∧ p4) ∨ True)) ∨ (((True ∧ True) ∨ True) ∧ (False ∧ p1))) ∨ p2) := by
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
theorem thm_5_vars_730146972068211880651232349831 : (((((p5 ∨ p1) → False) → (((False ∧ ((p1 → p1) ∨ True)) → (p5 ∨ ((p2 ∧ (p4 ∧ ((True → p3) → (p5 → p4)))) → p4))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225483308643972886450314906353 : (((p5 ∨ True) ∧ False) ∨ ((p1 → ((True → (p4 → p3)) ∧ ((((((p2 ∧ (p2 ∨ p4)) → p3) ∨ (True ∧ p4)) ∨ True) → p5) ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164472293738792999339891659388 : ((((((p2 ∨ True) → ((p1 ∨ p3) → (p1 ∨ p1))) ∨ ((False ∨ p2) ∨ p5)) ∨ p4) ∧ p1) ∨ ((False ∧ True) → (p1 ∧ (p1 → (p5 → p1))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175017096332051540846526393360 : ((p1 ∧ (((((False ∧ p2) ∧ p3) ∧ False) ∨ ((p5 ∧ p1) → p4)) ∨ (p2 → False))) → ((p4 → ((p4 ∧ p2) ∨ p5)) ∨ (False ∨ (True ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175008798255697613225515799950 : ((p1 ∧ (((p5 ∨ p1) → (((False → False) → ((p3 ∨ p2) ∧ False)) ∧ p1)) ∧ p5)) → ((False → (((True ∨ p4) → False) ∨ p3)) → (p2 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : (p5 ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : (False → False) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- False on the left can always be used.
    apply False.elim h12
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h13 := h10 h11
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57456711022165639281506143073 : (((p5 ∨ (True → p2)) ∨ ((((p3 ∧ (p1 ∨ p1)) → (p5 ∨ p4)) → (p4 → ((True → ((p1 ∨ False) → (p4 ∧ p3))) ∨ True))) ∨ p3)) ∨ p2) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322577850759786538293127398053 : (p5 ∨ ((p5 ∨ ((((p4 ∧ p2) ∨ False) → ((p2 → (((p1 ∨ (p3 → p2)) → ((p5 → True) ∧ p3)) ∨ p5)) ∧ (False → True))) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191604457472507564385280653646 : ((p3 ∧ (((True ∧ ((p2 ∨ p2) ∧ p2)) → p4) → p5)) ∨ ((((((p3 → p1) → p3) ∨ (True ∨ p1)) ∨ p1) → (False → p5)) ∧ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37918845363952407277697829702 : (((((True ∨ (p1 ∨ p5)) ∧ (((p5 ∨ (((False → True) ∧ p1) → ((False → (p2 ∨ p1)) ∧ p3))) → True) → p2)) ∧ (False ∨ p2)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238724124975068604907066436518 : ((p1 ∨ True) ∧ (((p3 ∨ ((False ∧ p1) ∨ (p4 → (((p1 ∨ True) → p3) → p3)))) ∨ ((p5 ∨ p5) ∨ ((p4 ∨ p1) → (True → p5)))) ∨ False)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323682419512716562738664986223 : (p5 ∨ ((p3 ∧ (True → ((p5 ∧ (((p2 → (p1 ∧ (p3 ∧ True))) ∨ p5) → p5)) ∧ (p4 ∨ (False ∨ p5))))) ∨ (p4 → ((p4 → True) → True)))) := by
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
theorem thm_5_vars_342382486147641760098711612759 : (p2 → (((p5 → (((p3 ∧ False) → ((p2 → p2) ∧ p4)) → ((p4 ∧ p2) → False))) ∨ p5) ∨ (False ∨ ((p1 ∨ p2) ∧ (True ∨ (p3 ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135657048785047693852392021581 : ((((True ∧ p5) ∧ (p2 → (p4 → ((True → (p5 ∨ p2)) ∧ (p5 ∧ (p4 ∨ p5)))))) → (p4 → ((False ∧ False) ∨ p1))) ∨ ((False ∧ p2) → p2)) := by
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
theorem thm_5_vars_134142009653316776270136708718 : (((((((p3 ∨ p5) ∨ (((p2 → (False ∨ p5)) ∧ p4) → p3)) ∨ (p3 ∨ True)) ∨ p2) ∧ (p5 ∨ (False ∨ p3))) ∨ p5) ∨ ((False → p4) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206252279453218852172226613689 : ((False ∨ ((p2 ∨ (p3 ∨ p1)) ∨ p2)) ∨ ((p3 ∨ (((((p5 ∨ ((p4 ∨ (p1 ∧ True)) ∧ (p2 ∧ False))) ∧ p3) ∧ True) ∧ p2) ∧ p1)) → p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h15.left
        let h18 := h15.right
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h15.left
        let h23 := h15.right
        -- False on the left can always be used.
        apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118195398770781218296274313232 : ((False ∨ (True → (((p3 ∧ ((((p1 → ((True ∨ p2) → p1)) → (p2 ∧ p1)) → (True ∧ (p5 ∧ p2))) ∧ p5)) → p5) → p2))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55455572779991432285864376195 : ((((p1 ∨ (False → (p2 ∨ p2))) → True) → ((False ∨ (((False ∨ p1) → p5) ∨ p5)) → ((((p1 ∧ p3) ∨ p5) ∨ (p1 ∨ p5)) → p5))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
          have h11 : (False ∨ p1) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h6
          -- We have shown the premise of h10, we can now drive its conclusion.
          let h12 := h10 h11
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- One of the premise coincides with the conclusion.
          exact h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h15 =>
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h18 =>
          -- One of the premise coincides with the conclusion.
          exact h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h21 =>
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
          have h24 : (False ∨ p1) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h20
          -- We have shown the premise of h23, we can now drive its conclusion.
          let h25 := h23 h24
          -- One of the premise coincides with the conclusion.
          exact h25
        case inr h26 =>
          -- One of the premise coincides with the conclusion.
          exact h26
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h28 =>
        -- False on the left can always be used.
        apply False.elim h28
      case inr h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- One of the premise coincides with the conclusion.
          exact h27
        case inr h31 =>
          -- One of the premise coincides with the conclusion.
          exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158024536195365116658695815361 : ((((p2 → False) → ((p2 ∨ True) → p4)) ∧ (((((p4 ∨ p3) ∨ True) ∨ (True ∨ p4)) → p3) ∨ p3)) ∨ ((True ∨ ((p1 ∨ p5) ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228595352143417929074033149007 : ((p1 ∨ (True → p3)) ∨ ((((False → p4) ∧ p1) ∧ (p3 ∧ (((False ∧ ((p1 ∧ p2) ∧ p4)) → (True ∨ (p2 ∨ False))) ∨ (True → False)))) → p3)) := by
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
  let h6 := h3.left
  let h7 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21412530452174756088649264250 : ((((((p2 ∨ p2) ∧ (p2 ∧ p3)) ∧ (False ∧ p5)) ∨ p2) ∨ ((False ∨ p2) → (((p1 ∨ ((p3 ∨ (p5 ∧ p5)) → False)) ∧ p3) → p1))) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h11 : (p3 ∨ (p5 ∧ p5)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h12 := h8 h11
      -- False on the left can always be used.
      apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51166600723264020018598691022 : ((((p3 ∨ ((p4 ∨ (p2 → p1)) ∨ (False ∧ (True → ((p4 ∧ p1) → p1))))) ∧ (True → p4)) ∨ ((p5 ∨ p5) ∨ (False → (p2 → p2)))) ∨ p2) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255161100472446583506608612385 : ((p4 ∧ p3) → (p4 ∧ ((((p5 ∧ False) ∧ ((True ∧ False) ∧ p3)) ∨ (p1 ∧ p1)) ∨ ((((True ∧ p5) → (False ∨ (p3 ∧ True))) ∧ p3) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309933383190279200755797709827 : (p2 ∨ (((p4 ∧ p3) → (((p2 ∧ (p2 ∧ p3)) ∨ ((((p2 ∧ True) ∨ p4) ∧ p1) → True)) → p1)) ∨ (True ∨ (p1 ∨ ((p3 → False) ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322409910941863589714274883555 : (p5 ∨ (((((p2 ∨ (p2 ∨ p4)) → (p4 ∧ True)) ∧ (p5 → p5)) ∧ ((p5 ∧ p5) ∨ (p4 ∨ (p3 → (p5 ∨ (p1 ∨ (p1 ∧ False))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49784381750969750650337985245 : (((p3 ∨ (p5 ∧ (((p5 ∨ p4) ∧ p3) → ((((((p4 ∧ p3) → False) → p3) ∨ (p2 ∨ p4)) ∨ p3) → p3)))) → (p3 ∧ (True ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47211112227784118976513440513 : (((((p2 ∨ (p3 ∨ (False ∨ (False ∧ (p3 ∧ True))))) ∨ p1) ∨ ((((p5 ∧ (p5 ∨ p4)) ∧ (p4 ∧ False)) → False) ∨ True)) ∨ (p4 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624432272124267172771994583669 : ((((p3 ∨ (p3 ∨ (p5 ∨ ((p5 ∧ ((p1 → True) ∧ True)) ∨ (((p5 ∧ p3) ∨ ((p5 → False) ∨ True)) ∨ (False ∨ (p1 → p5))))))) ∨ p2) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_204228737178281790407808810948 : ((((p2 → (p2 ∨ p1)) → p2) ∧ p1) ∨ ((False ∨ (p3 → p4)) ∨ ((p1 → True) ∨ (False ∧ (p5 ∧ ((p2 ∨ p4) ∧ ((p2 ∧ p2) ∧ p1))))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167822905345087150886250616282 : (((False ∨ (p3 → ((p1 → p4) ∧ ((False → p4) ∧ True)))) ∧ ((p2 ∨ True) → (True → p3))) → ((((False ∨ (p5 → p1)) → p3) → False) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225636952573393158328238133313 : (((p1 → p5) ∧ p2) ∨ ((((p1 ∧ (True ∨ (p2 ∧ (p1 ∧ False)))) ∧ (p1 ∧ (True → False))) ∧ p4) ∨ ((False ∨ True) → ((True ∨ p1) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654407322297264811076784915541 : ((((((p5 ∨ ((p1 → False) → p5)) ∧ (p1 ∧ ((False ∧ (((p4 → (False ∧ p3)) ∨ p3) → (False ∨ False))) ∨ p1))) ∨ True) ∨ (p5 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_943514330540059783626393440721 : ((((p4 ∧ ((False ∨ True) → False)) ∧ (((p1 ∨ True) ∧ ((False ∧ ((p1 → p1) ∨ False)) → ((p1 ∧ ((p1 ∨ p3) ∧ p1)) ∧ False))) ∧ p4)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h12 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h12
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719669546314990322439502780533 : ((((True → ((False → p5) → p5)) ∨ (((((p4 ∨ (True → (p3 → p1))) ∧ p5) ∨ p3) ∧ p1) → (p3 ∨ (p5 ∧ ((p1 ∨ p3) → p1))))) ∨ p4) ∧ True) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Implications on the right can always be decomposed.
      intro h12
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336094814159726842155091492919 : (p1 → (((False ∧ (p3 ∨ ((((p5 → p5) ∧ ((p1 → p5) ∨ (p4 ∧ p3))) ∨ ((p5 → (p1 ∧ p5)) → False)) ∨ (p1 ∨ p3)))) ∧ p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208741476483615016281222132257 : ((p1 ∧ (p4 ∧ (False → (p1 ∧ p1)))) → (((((True → (((True ∧ False) → p1) → p3)) ∧ p4) ∨ (False → ((p3 → p1) → p2))) ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304695216912356512830853683977 : (p1 ∨ (((((p4 → p5) ∨ ((p4 ∧ True) → (((p5 ∧ (True ∨ (p3 ∨ False))) ∧ ((False ∨ False) → p1)) → p5))) ∧ p2) → False) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677888427963748303479079540771 : (((((((p1 ∨ (((p3 → (p5 → p1)) ∧ p5) → p5)) → p2) → ((p1 ∧ p5) ∧ p1)) ∨ (p1 → True)) ∨ ((True → (True ∧ False)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53276203799472101528720806500 : (((p2 ∧ ((True ∧ (((p3 → p3) → p3) → False)) → (p3 ∨ p4))) ∨ (((p1 → p1) → True) ∨ ((False ∧ (p3 ∧ (p1 ∨ p4))) → p3))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42644442447615028926702791351 : (((p4 ∨ ((((((((p3 → (p3 → True)) ∨ p3) → p4) ∧ (False ∧ (True → p3))) → p4) ∨ (p4 ∧ p1)) → (p4 → p1)) ∧ p3)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354563526397489430132848742593 : (p5 → ((((((p1 ∨ False) ∧ p4) ∧ (((p2 ∧ ((p4 ∨ (p5 → p4)) → p1)) → p3) ∧ (p5 ∨ ((p2 → p5) ∧ p1)))) ∨ p2) ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67777456019756039374634309032 : ((p2 → ((p4 ∧ ((p1 ∨ (p1 ∨ (True ∧ p2))) → ((p4 ∧ ((p1 ∨ (((p1 ∨ p5) ∨ True) ∨ (p3 → p3))) → p1)) ∨ p4))) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172147300531678145098509427623 : (((p1 → (((p5 → ((p2 ∨ p2) → p4)) ∧ False) ∨ p3)) ∧ (p5 → (p4 → p2))) ∨ (p2 → (p5 ∨ ((p3 ∨ p5) ∨ ((p5 ∨ p3) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_645214019134851705566475235802 : ((((p3 ∨ ((True ∨ True) → ((p2 ∨ (True → (p1 ∧ True))) ∨ (((p4 → p5) ∧ ((((p2 → False) ∨ True) ∧ p2) ∧ p5)) ∨ p5)))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609666022231286870118757800711 : (((((p1 ∨ ((p5 ∧ (((p3 ∧ ((p5 → (True → (p1 ∨ p1))) ∨ p4)) ∧ True) ∧ ((p1 ∧ (p1 → True)) ∨ p5))) ∧ True)) ∨ True) ∨ p5) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324600522345295848792922052631 : (p5 ∨ ((True ∧ (False → True)) ∧ ((p1 ∨ p2) ∨ ((p3 ∧ ((p1 → p4) ∨ p5)) ∨ (True ∨ ((((p2 ∧ p3) → p2) → p4) ∧ (p4 ∧ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41096244708744903966026287049 : ((((((p4 ∧ False) ∨ (p3 → ((p1 ∧ ((p4 ∧ (p4 → False)) ∧ p5)) ∨ False))) ∧ (False ∧ (p3 → True))) ∧ (p2 ∧ (p1 → p4))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311805602009554751569483433538 : (p2 ∨ (p1 ∨ (((p4 ∨ (p4 ∨ p5)) → ((p4 ∨ True) → ((p2 ∨ p5) → (p1 → ((p3 ∨ p1) ∧ ((p2 → p5) → (p1 ∨ p2))))))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
  -- Implications on the right can always be decomposed.
  intro h27
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h28 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h30 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h33 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
    case inr h34 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h35 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h36 =>
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h37 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h38 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
  case inr h39 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h40 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h41 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h42 =>
        -- Disjunctions on the left can always be decomposed.
        cases h42
        case inl h43 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h44 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
    case inr h45 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h46 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h47 =>
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h48 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h49 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68605170826522750534225492546 : ((p4 → ((((((p1 ∨ True) ∨ p3) ∧ (p4 → (((False ∨ p2) ∨ ((p2 ∨ False) ∨ True)) ∨ p2))) ∨ ((p5 → True) → p4)) → p3) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205647896009321723271103073132 : (((p5 ∧ p4) ∨ ((True → False) ∧ p3)) ∨ ((p5 ∨ ((((p2 ∨ (False ∨ True)) ∨ (p4 ∧ p1)) → p3) → p1)) ∨ ((p5 → True) ∨ (p5 → p1)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176947155219560892789391416718 : (((p5 → p5) ∨ (p5 ∧ ((((False ∨ p3) ∨ p2) ∧ (True ∨ p4)) ∧ p2))) ∧ (p2 ∨ ((True ∧ (((p4 ∧ p3) ∧ p3) ∧ (p4 ∨ True))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168318555877932561242666837360 : (((False → p5) ∧ (((p5 ∨ (p1 ∨ (p4 → (p4 ∧ True)))) → False) ∨ ((False ∨ p1) ∧ p2))) → ((((True → False) ∧ (p2 → p2)) ∧ p4) → p5)) := by
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
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h18 := h5 h17
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135944285896353957872654293016 : (((((((False ∨ True) ∧ p3) ∨ p4) → p5) ∧ (p4 → False)) ∧ (((p1 ∨ True) ∧ p1) ∧ ((p4 ∧ (p1 ∧ p5)) ∧ p2))) ∨ ((p5 ∧ False) → p2)) := by
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
theorem thm_5_vars_47208012396130530280771059363 : ((((p1 ∧ ((p1 → (((p5 ∧ p1) → p4) ∧ False)) ∨ p4)) ∧ (((p1 ∧ (p5 → p5)) ∧ p5) ∧ (True ∧ (p1 ∨ p2)))) ∨ (p3 → p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135082792351430382987782912751 : (((((((p5 → ((True → p5) ∨ p3)) → p3) → p4) ∨ (False ∧ (p1 → p5))) → ((p2 ∨ p1) ∧ p5)) ∨ (False ∨ True)) ∨ ((p4 ∨ p2) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175084109376447300637133469701 : ((p3 ∧ (((p4 → p2) → p1) ∨ (p1 → (p1 ∧ ((p2 ∧ (p4 ∧ p3)) ∨ False))))) → ((False ∧ (((p3 → p5) ∨ p3) → p2)) ∨ (p3 ∨ p1))) := by
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
theorem thm_5_vars_654936422683682827319435671973 : ((((((False → (p2 → (p5 → (p3 ∨ p4)))) ∨ (p5 ∨ (False ∧ (p2 ∨ ((p2 ∨ ((p3 ∨ p4) ∧ False)) ∨ p1))))) → p3) ∨ (True ∧ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644061857873295700252300087047 : ((((True ∨ ((((((p1 → False) ∨ p2) ∨ False) → False) ∨ p5) ∨ (((p3 ∨ ((p4 ∧ (True ∨ p2)) ∧ p5)) ∨ (p1 → p5)) → p1))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147246188960084421566487420824 : (((((p2 ∨ (p5 ∧ False)) ∧ ((p2 ∧ (p4 ∧ p3)) → ((True → p5) ∧ (p2 ∨ (p3 ∨ p3))))) ∧ True) ∨ p3) ∨ ((p1 ∨ p1) → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618053049173448447812247939791 : ((((((False → (p4 → False)) → False) ∧ (((True ∧ ((p4 → ((True ∧ p4) → p4)) ∧ (p4 → (p2 → p5)))) ∨ (False → False)) → p5)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_173790082099345521513138265992 : ((((p1 → True) → (((True ∨ (p5 → (p1 ∨ p5))) ∨ p1) → (True ∨ p4))) ∨ p5) → ((((p5 → p5) ∧ (p4 ∧ True)) → (p5 ∧ p4)) ∨ True)) := by
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
theorem thm_5_vars_314765400992915399168846477269 : (p3 ∨ (((p4 ∨ ((p3 ∨ (p3 → ((p2 → (p5 ∨ p4)) ∧ p5))) ∨ p2)) ∧ True) → ((((p5 ∨ (False → (False ∨ p4))) ∨ p3) ∨ p3) ∨ p2))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617867460381608365205216496249 : (((((((True ∨ p1) → True) ∨ (False ∨ p3)) → ((((p5 ∨ ((p3 → False) → (p5 ∨ p3))) → True) ∧ (p2 ∨ True)) → (p5 ∧ p2))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_113457264092558864872062433497 : (((((((p1 ∧ p3) ∧ p3) ∧ ((((p2 → False) ∧ p3) ∨ (p4 ∧ False)) → (p5 → p1))) ∧ (p2 → p4)) → p5) ∨ (True → True)) ∨ (p5 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43638974505390694375058335759 : (((((False ∨ (p5 ∧ ((p3 ∧ (p5 ∨ (p3 ∧ (p3 → ((p3 ∧ (p2 ∨ p3)) ∧ p2))))) ∨ (p1 ∨ p1)))) ∨ (p2 → True)) → False) → p3) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ (p5 ∧ ((p3 ∧ (p5 ∨ (p3 ∧ (p3 → ((p3 ∧ (p2 ∨ p3)) ∧ p2))))) ∨ (p1 ∨ p1)))) ∨ (p2 → True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172046752916125006454875292176 : (((p4 → (((True → ((True → False) → (p4 ∧ True))) ∨ p1) → p1)) ∨ (p5 ∨ p3)) ∨ (((p2 ∧ (p3 ∨ (p2 ∧ False))) ∧ (False ∨ False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



