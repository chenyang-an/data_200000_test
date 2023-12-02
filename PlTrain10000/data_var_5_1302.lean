variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186535317361047844808493732757 : ((((((True → p1) → p2) ∨ p2) ∧ (p2 → p3)) ∨ (p4 ∨ True)) → (p5 → ((p2 → p2) → (((p1 ∨ p2) ∧ True) → ((p3 ∨ p5) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
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
        exact h2
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h20 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h21 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h24 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186239760370795225054898907292 : (((((True ∧ ((p2 ∧ p2) ∧ (p2 ∨ p2))) ∨ p3) ∧ False) → p1) → (p1 ∨ ((p3 → p2) ∨ (True ∨ (((p1 ∧ p4) ∨ (p1 ∧ p5)) ∧ False))))) := by
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
theorem thm_5_vars_623603599730642880243751079132 : ((((False ∨ (p3 ∨ ((p3 → ((p3 → ((p3 → p2) → (True → ((p2 → p4) ∧ (p1 ∧ p3))))) ∨ (True ∨ p5))) ∨ (p5 → True)))) ∨ p3) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59682245133702418031069940448 : (((True ∧ p4) → (((p5 ∨ (p5 ∨ (p5 → (p1 ∧ (((p3 ∧ p3) ∧ p1) ∧ ((p4 ∨ p1) ∨ True)))))) → (p1 → (p2 ∧ True))) ∨ p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18003677339614825993006639900 : (((((False ∨ False) ∧ p5) ∨ (p5 ∧ (((p3 ∧ (p4 → p2)) → ((False ∧ p2) ∧ (p1 ∧ p2))) → False))) ∨ (False → (True → (p3 → p2)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48412545035531464600858225019 : (((p2 → ((p5 ∧ ((p3 ∧ p2) → (p1 ∧ (p3 ∧ ((p4 ∨ ((p5 ∧ p5) → p2)) ∨ (True ∨ p2)))))) ∨ (p4 ∨ False))) → (p3 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325087596724830508040824520847 : (p5 ∨ ((False → p1) → (p2 → (((p3 → p5) ∨ (p1 ∨ ((p3 ∨ p1) → ((p5 ∧ (p2 ∧ p1)) ∧ ((p2 → (p3 ∧ p3)) → True))))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314633371338587475105745453887 : (p3 ∨ ((p3 ∨ (((p3 → (p5 → (((p1 ∨ (p4 → p4)) → False) ∨ True))) ∨ p2) ∨ True)) ∧ (p1 ∨ (p1 ∨ ((p4 ∨ False) → (False → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_157760617199555333087480025551 : (((True ∧ ((p2 ∨ ((p3 → p1) ∧ p3)) → (p5 ∨ (p2 ∨ True)))) ∧ ((p4 ∨ p4) → (True → False))) ∨ ((((p3 → p2) ∧ p5) → p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112013739537529709841125737232 : ((((True → (p3 ∨ (p1 ∧ p2))) → ((((p1 ∨ p5) ∧ p1) ∨ (((p2 → (p3 ∧ p3)) → p3) ∧ p3)) ∨ (p3 ∨ p2))) ∨ p5) ∨ (False ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168306332240134510377410421158 : (((p4 ∨ True) ∧ ((p3 ∨ ((True ∨ p5) ∧ False)) ∨ ((p1 ∨ p1) ∨ (p5 ∧ (True → p4))))) → (p5 ∨ (p2 ∨ ((False ∨ p2) → (True ∨ p2))))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- False on the left can always be used.
          apply False.elim h8
        case inr h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h12
        case inr h14 =>
          -- False on the left can always be used.
          apply False.elim h12
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- False on the left can always be used.
            apply False.elim h19
          case inr h20 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h22
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- False on the left can always be used.
            apply False.elim h23
          case inr h24 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h26
  case inr h28 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h31
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- False on the left can always be used.
          apply False.elim h32
        case inr h33 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h34.left
        let h36 := h34.right
        -- Disjunctions on the left can always be decomposed.
        cases h35
        case inl h37 =>
          -- False on the left can always be used.
          apply False.elim h36
        case inr h38 =>
          -- False on the left can always be used.
          apply False.elim h36
    case inr h39 =>
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h40 =>
        -- Disjunctions on the left can always be decomposed.
        cases h40
        case inl h41 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h42
          -- Disjunctions on the left can always be decomposed.
          cases h42
          case inl h43 =>
            -- False on the left can always be used.
            apply False.elim h43
          case inr h44 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h45 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h46
          -- Disjunctions on the left can always be decomposed.
          cases h46
          case inl h47 =>
            -- False on the left can always be used.
            apply False.elim h47
          case inr h48 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h49 =>
        -- Conjunctions on the left can always be decomposed.
        let h50 := h49.left
        let h51 := h49.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h50



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151847423580238983385045454203 : ((((p2 ∨ (((False ∧ (p3 → True)) → p2) ∧ ((True → p2) ∧ p5))) → p4) ∨ (False → ((p1 ∧ p2) → p5))) → ((p4 ∧ p4) ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157793536030630992257660402481 : ((((p1 → True) → (p5 → ((p1 ∨ p1) ∨ ((p1 ∧ p5) ∨ p3)))) ∨ ((p3 ∧ False) ∧ (p4 → p5))) ∨ (False → ((p1 ∧ p2) ∧ (p4 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356149662312105261221915393715 : (p5 → (((False ∧ ((p4 ∧ False) ∧ ((True → (((p4 → p4) ∧ p5) ∨ p1)) ∧ True))) ∧ (False ∧ p2)) ∨ ((p1 ∧ p4) ∨ ((True ∨ False) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171669094837543457483331861570 : (((p5 ∧ ((p4 ∧ (p5 → p4)) → (p5 ∨ (True ∧ ((p1 ∧ p3) ∨ p5))))) ∨ True) ∨ (((p3 ∨ (True ∨ (p1 → p1))) ∨ p1) ∧ (p1 ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713783317575378909286560627866 : ((((((False ∨ (p2 → p4)) ∧ p2) ∨ p3) → ((p2 → (p3 ∧ p3)) ∧ ((((p5 ∨ (p1 → p1)) ∧ p5) ∧ (p3 ∨ p5)) → (p3 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160590069678989336155788202737 : ((((p5 ∧ ((p4 ∨ p2) ∧ ((True → p5) ∨ True))) ∨ False) ∧ (p2 → ((p2 ∧ p5) → (p1 → p2)))) → ((p4 ∨ p5) → (p4 → (False ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h1.left
    let h21 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h29 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h32 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h33 =>
      -- False on the left can always be used.
      apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158656483138771139375220144630 : ((p1 ∧ (p1 ∧ (p3 ∧ (p5 → (p4 → (((p2 → (p3 ∧ p5)) ∨ (p1 ∨ (p2 ∧ p2))) → p2)))))) ∨ (((p5 → p5) ∧ (False → p1)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119086683212335116626464813697 : ((p1 → (((((False → p1) ∧ (p1 ∧ p1)) → (p2 ∨ (p4 ∨ (p2 ∨ p5)))) → p3) → ((True → ((p3 → p4) ∧ p2)) → p2))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678301718324882541731334357977 : (((((((p3 → (p5 ∨ p5)) ∨ (p4 ∧ False)) ∧ True) → ((True → (True → (p4 ∧ (True → p3)))) ∧ p5)) ∨ ((p2 → p2) ∨ (p4 → p5))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52778319053619813455625921734 : ((((False → ((p1 ∨ ((p4 ∧ True) ∨ p1)) ∨ (p5 → p2))) ∧ (True ∧ p2)) → ((((p1 ∨ (p3 ∨ True)) ∧ p1) ∧ False) ∨ (False ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57081196927251955089572697631 : ((((False ∧ p4) ∧ p5) ∨ ((p5 ∧ (p1 ∨ p1)) ∨ ((p1 → (p3 → p2)) → (p4 ∨ (((p5 ∨ p2) ∨ ((p1 ∧ p2) → p5)) ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185529132836577984474827190958 : ((p3 ∨ (((p3 ∧ (p1 ∧ p3)) ∧ p5) ∨ (p3 → (False → p3)))) ∨ ((False ∧ (p1 ∨ p2)) ∧ (((False ∨ (p1 → p4)) → p1) → (False → True)))) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58179413339087707873737552686 : (((p3 ∧ p2) ∧ (p3 ∨ (((False → (p4 ∨ (True ∨ ((((p4 → p1) ∨ p3) → p1) → False)))) ∧ (p3 → p1)) → (p5 ∨ (p3 ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311175200159275233681382573384 : (p2 ∨ ((True ∨ p4) → (((((((((p1 → p2) ∨ p1) → p5) ∨ False) ∧ False) ∧ (p1 → ((p1 ∨ (p2 → False)) ∧ True))) ∧ False) ∨ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_158731428716392020318403184465 : ((p3 ∧ (p2 ∧ (((((p5 → p5) → p3) → p4) ∨ (((p1 → (True ∨ p5)) ∧ False) ∧ p3)) ∨ p1))) ∨ ((True → ((p5 ∧ False) ∧ p1)) → False)) := by
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44182238864718293905670355734 : ((((True → (((p1 ∨ p2) → (((p3 ∨ True) ∧ (True ∨ (p5 → p4))) → ((p1 ∨ p2) ∧ p5))) ∨ p3)) → ((False → p3) → p5)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111285518063347635092893399662 : ((((False → p4) → (((False ∨ (True → p4)) ∧ ((p1 → p5) ∨ ((p5 → p1) → ((False ∨ (p3 ∧ p1)) ∧ p3)))) ∧ True)) ∧ True) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803429430567286055169208010285 : (((p3 → ((p3 → ((p4 ∨ p5) ∧ ((p1 ∨ (p1 ∧ p3)) ∧ ((False → False) ∧ (((p3 → p3) → p2) ∧ (p5 ∧ (p2 ∧ True))))))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265875394145432102235509947838 : (True ∧ (True → ((((((True ∨ p4) ∨ (True ∨ (p4 → p3))) ∧ (((p2 → (True ∧ p2)) → False) ∨ False)) ∨ ((False ∨ p4) → False)) ∧ p4) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44481214715523356994753054301 : ((((True ∨ (False ∧ ((p2 ∧ (True ∨ ((p4 ∧ p3) ∨ True))) ∧ True))) → (True → (p1 → (((p5 ∨ p4) ∧ (p1 ∧ True)) ∧ False)))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115747274057390721498013339085 : ((((p2 ∨ True) → (p3 ∨ (p2 → p4))) → ((False ∨ (((((True ∨ (p1 → (p2 ∧ p4))) ∧ p3) → p4) ∧ True) ∧ p5)) → p1)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254496779840011793657486006317 : ((p3 ∧ True) → (p2 ∨ (((((p3 → p3) ∨ ((((p1 ∧ (False → ((p3 → False) ∧ (p2 ∧ p4)))) ∨ p5) → p3) ∨ p1)) ∨ False) → p5) ∨ True))) := by
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
theorem thm_5_vars_241543591242303319799810448181 : ((False → p3) ∧ (((p3 ∨ ((p5 ∨ p3) → p3)) → p4) → (((((p3 → p5) ∨ (p5 ∧ ((p5 ∧ True) → (p5 ∨ p3)))) → p3) ∨ True) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161172146521682231657030022810 : (((p5 ∧ p1) ∨ (((True → (p3 ∧ (p1 → p2))) ∧ (((p1 ∧ p1) ∨ (True → p5)) → p4)) ∧ p2)) → (((p3 ∨ p3) ∨ p2) ∨ (False → p4))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310042847812013793219131821273 : (p2 ∨ ((p3 ∨ (((p2 ∧ p5) ∨ ((p1 → p3) ∨ (((False ∧ True) ∧ True) ∧ p2))) → p2)) ∨ (p2 → ((((p5 ∧ p2) ∧ False) → p5) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324170157877535179157352913589 : (p5 ∨ (((((p3 ∧ p3) ∨ p1) ∧ p5) ∨ ((p1 ∧ True) → True)) ∨ ((((p5 ∧ p2) ∧ ((True ∨ p5) → False)) → ((p2 → p2) ∧ False)) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232871579497989267438476061329 : ((p2 ∧ (p4 → True)) → (((p5 → (p2 ∨ p1)) → (p3 → p5)) ∨ (False → (((p2 → ((p4 ∧ p1) → (p4 ∧ False))) ∧ (False ∨ False)) ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h9 := h6.left
  let h10 := h6.right
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660282151556214604954249199998 : (((((True ∧ (p5 ∨ (((p3 ∨ p4) → ((p4 ∨ p3) ∧ (p4 ∧ p5))) ∨ ((True ∧ ((p2 → p2) → True)) ∧ p2)))) ∨ p4) → (p2 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317962826868394370679236937339 : (p4 ∨ ((True → ((p2 ∧ p3) ∨ ((p4 ∨ (((p2 ∧ (p4 → ((p2 ∨ p1) ∨ True))) ∧ ((p1 → True) ∨ p4)) ∨ p1)) ∧ (True → p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346896341031341920573795423983 : (p3 → ((((((True → (((False → False) ∨ ((p3 ∨ p1) → True)) → p5)) → p4) ∨ p3) → p5) ∨ p2) ∨ (p3 ∨ (False ∨ ((p2 ∧ p2) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148143674332822242040580942092 : (((p5 ∧ ((((p1 ∨ p1) → p4) ∨ p3) ∧ (((p2 ∨ True) ∧ (p1 ∨ p3)) ∧ (True ∨ p3)))) → (p2 ∧ p4)) ∨ ((p3 → p3) → (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44711760074664493834565527398 : ((((p2 ∧ (False ∨ (p3 ∧ True))) ∧ ((((((False → True) → True) ∧ p4) → False) ∧ ((True → (p1 ∧ True)) → p3)) ∧ (p1 → p5))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_486677205090165509603068292211 : ((((p2 ∨ (((p2 ∨ p4) ∧ p5) ∨ p3)) ∨ ((((True ∧ ((p3 ∧ (p1 ∧ p4)) → p1)) → (p5 → (False → p4))) → (p4 ∨ p1)) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65112936624915566858730700290 : ((p2 ∨ (p5 ∨ (((True ∧ ((p5 ∧ p5) ∨ ((p3 ∧ ((True ∧ ((p5 → (True ∧ p1)) → p3)) ∨ True)) ∨ True))) ∨ p4) ∨ (p2 ∧ p1)))) ∨ p2) := by
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
theorem thm_5_vars_354790429769579079867973411959 : (p5 → (((((p3 ∨ False) ∧ p2) → (p2 ∨ False)) ∧ (((p5 → p3) ∨ ((p3 ∧ p4) ∧ (p3 ∨ p3))) ∧ (True → (True → (p3 → p1))))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783018276105129150798944040683 : (((p3 ∨ ((p1 ∧ ((((p4 → (((p2 ∨ p3) → (p5 ∧ (False ∧ False))) → p2)) ∧ False) ∨ p2) ∨ ((p1 ∧ p1) ∨ p5))) ∨ (True → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48876759970977187654754729765 : (((True → (True ∧ ((((p3 → (False ∧ p3)) → (p1 ∨ True)) ∧ p2) ∨ (((p5 ∨ p5) ∧ p3) ∨ (True ∨ p5))))) ∧ (p3 ∨ (True ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131537281513809839138192231622 : ((((p5 ∨ False) → True) ∧ ((((p5 ∧ ((((p4 ∧ p5) ∨ (p4 ∧ p4)) ∨ (p1 → p5)) ∨ False)) ∧ p4) ∨ True) ∨ False)) ∧ ((p5 ∧ p4) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59275296410320083508050641215 : (((p3 ∨ p1) ∨ (p2 ∧ (((p3 → p1) ∧ (True ∨ ((p4 → p5) ∧ ((True → (p4 ∧ False)) ∧ ((p1 ∧ (p3 ∨ p4)) ∨ False))))) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112977866318896512795782411551 : (((p2 ∧ ((((p4 → False) ∧ p4) ∧ ((((p1 ∧ True) ∧ (True ∧ p1)) → p5) ∧ (((p3 ∧ True) → p1) ∧ True))) ∧ p4)) → False) ∨ (p5 → p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h7.left
  let h11 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h14 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h15 := h8 h14
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657040821862426911702218527661 : ((((((p3 ∧ p3) → p3) ∧ ((p2 → ((p3 ∧ ((True ∨ (p1 → p2)) ∨ (p4 ∨ ((True ∧ p2) ∧ p1)))) ∧ True)) → p3)) ∨ (False ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213111518056055305434462357718 : ((((p3 ∨ p5) ∧ p3) ∧ False) ∨ (p2 ∨ ((p5 → ((((p3 → p3) → (p2 ∨ (p3 ∧ p3))) → p5) → (True ∨ p2))) ∨ (p1 ∧ (p1 → p4))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322511590377049483033742808438 : (p5 ∨ ((False ∧ ((True ∧ ((((p4 → (p4 ∧ p3)) ∧ False) ∧ (p1 → p1)) → (p1 ∧ p1))) → (p4 ∧ (True → (p5 ∨ (p3 ∨ p2)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258280324080005797606818116366 : ((p5 ∨ True) → (((p3 ∧ p4) → (p2 → (((p3 → (p1 ∨ ((p4 → (p3 ∨ ((p3 ∧ p3) ∧ False))) ∧ p1))) ∨ (False → False)) ∨ p2))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62282572698508330141035087123 : ((p3 ∧ (((p3 → (p3 → (p5 ∧ p4))) → (p4 ∨ ((p2 → (((p5 ∧ ((p5 ∨ False) → (p1 ∨ p1))) ∨ p3) ∧ p5)) → True))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647244885203135472175969035752 : ((((p4 → ((p3 ∧ (p4 → ((p5 ∧ (((p3 → ((p3 ∧ (p3 ∨ (False ∧ p5))) ∨ False)) ∧ p2) → (p4 ∨ p2))) ∧ p3))) ∧ True)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113524567103395341091737317894 : ((((p3 ∨ (p3 ∧ (p5 → (p1 ∨ (p4 ∧ p3))))) ∧ ((True → ((True → (True → False)) → (p2 → p5))) ∨ p4)) ∨ (p1 ∧ p2)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134158455774354476854466482934 : ((((((p1 ∨ True) → ((((p4 ∧ True) → p5) → p3) ∧ False)) ∨ ((True ∨ p1) ∧ p1)) → ((p1 ∧ p3) ∧ p3)) ∨ p2) ∨ (p3 → (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137810186133549605297623233308 : ((p3 ∨ (((p2 ∧ ((p3 ∧ (p4 ∧ (p5 ∨ ((p2 → (True ∧ p2)) ∧ p4)))) ∨ (p2 ∨ p5))) ∧ (False ∧ True)) ∧ p1)) ∨ (True ∧ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211274993725525851528692245036 : (((p4 ∧ p1) ∨ (p1 ∨ True)) ∧ (((True → (p1 → p3)) ∧ p3) → (((p1 ∨ False) ∧ ((False ∧ p3) ∨ p5)) ∨ ((p1 ∧ p2) → (p1 ∨ p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148678360531710954918256174996 : (((((True ∨ p3) ∧ (p3 ∨ p5)) ∧ (p1 ∧ p2)) ∨ (p5 ∧ ((((p4 → p3) → p3) ∧ p2) ∧ (False ∧ p2)))) ∨ (p5 → (p1 → (p3 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41827211065257280160875380661 : (((((p3 ∨ p5) → True) ∧ (p4 ∧ (p5 ∨ (((p3 ∨ ((p1 → True) → True)) ∧ ((True → False) ∧ (p3 → p5))) → (p1 → False))))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52620166197830865508896978565 : (((((True ∧ p2) → p5) ∨ (p4 ∨ (p5 ∨ (p5 → ((p5 → p4) ∧ p1))))) ∨ ((True → p1) ∨ (p2 ∨ ((p2 ∨ p2) → (p4 ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259883001166500252154023072411 : ((p1 → p4) → (((p4 ∧ (p5 ∧ p5)) → (p4 → p4)) ∧ (((p1 ∨ p1) ∧ ((p5 ∨ p4) → (p1 ∧ p4))) ∨ (((True ∨ p3) ∨ p2) ∨ True)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311203435679206639657299815638 : (p2 ∨ ((p4 ∨ p4) → (((p4 ∧ p4) → ((p3 → (p2 ∨ True)) → ((False ∨ p5) ∧ ((p2 ∨ (p3 → ((False ∧ p2) ∧ p5))) ∨ p4)))) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (p4 ∧ p4) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p3 → (p2 ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h6
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : (p4 ∧ p4) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h12
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h13
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : (p3 → (p2 ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h16
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h17 := h14 h15
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- One of the premise coincides with the conclusion.
      exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314772337568819955425105947104 : (p3 ∨ ((((p3 ∨ True) ∧ (p3 ∨ ((p2 → False) ∨ (p4 → p2)))) ∧ (True → p4)) → ((p2 ∨ (True ∨ (True ∧ (p2 ∨ p4)))) ∨ (p4 ∨ p4)))) := by
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
    cases h5
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133901477972515700418508954737 : (((p1 ∨ (((p3 → (p4 ∨ p1)) → (p4 ∨ p3)) → ((p4 → (p2 ∧ p1)) ∨ (((True ∧ True) ∨ p5) ∨ True)))) ∧ False) ∨ (False → (p3 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133864443932454248097467608718 : (((p2 ∧ ((p5 ∨ (p5 ∧ True)) ∧ ((p1 ∨ ((p4 ∨ (p1 ∧ ((p5 ∨ (p5 ∨ p1)) ∧ p1))) ∧ False)) ∧ p4))) ∧ p3) ∨ ((p5 ∧ False) → p2)) := by
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
theorem thm_5_vars_248684409520127182284033712858 : ((p3 ∨ p2) ∨ ((((False ∨ (p1 ∨ p3)) → p3) → ((p4 ∧ (p2 ∧ ((True ∧ p2) ∨ (False → (p3 ∧ (p5 ∨ True)))))) ∧ (p3 → p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1514897276009958987676779448 : (((((p4 ∧ (False ∧ False)) ∧ p3) → ((p4 → p4) ∧ p2)) → ((((p2 → True) → p1) ∨ (p1 ∨ (p5 ∨ True))) → p1)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797817542252181039260746064683 : (((p1 → ((True ∧ (((((p5 ∧ (p2 → ((p1 ∨ p2) → p3))) → ((False → True) → (p2 ∨ True))) → True) → p5) ∨ True)) ∧ (False ∨ p1))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687091549295860303135559797625 : ((((p1 → (((((False ∨ ((p1 → p3) ∧ p1)) → (p2 → (p2 ∧ p3))) → p5) ∨ True) ∧ True)) → ((True → (p1 ∧ p2)) ∨ (p1 → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245647192857141961500260302866 : ((p3 ∧ p1) ∨ ((((((p1 ∧ False) → (p3 ∧ False)) → (p3 ∨ (p3 ∨ p5))) → (p4 ∧ p2)) → (p2 → (p1 → ((p4 ∨ p1) ∨ True)))) ∨ p5)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620200953598373068595950461017 : (((((p3 ∧ p4) ∨ (((p3 ∨ (((True ∧ p1) ∨ (p3 ∨ (p4 ∨ p4))) ∧ (p5 ∨ p3))) ∨ (False ∧ ((p3 ∧ p3) → p4))) ∨ p3)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66318431480204279331752129186 : ((p5 ∨ (True ∧ (p4 ∨ (p1 → (False ∨ ((True → (p1 → ((False ∨ False) → ((p1 → ((p1 ∨ (p5 ∨ p1)) → p3)) → p5)))) → p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111573947220898999484552728801 : (((((p2 ∧ True) ∨ (p3 ∨ ((((p3 → (p3 ∨ ((p5 ∧ (p1 ∧ p1)) → p1))) → p4) → (p3 ∧ p1)) ∧ p4))) ∧ p1) ∨ p2) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711850767008445223514793543994 : (((((False ∧ (p4 ∧ (p2 ∨ p5))) ∧ p1) ∨ (p5 → (((p1 ∧ p5) ∧ (False ∨ (p5 ∧ ((p4 ∧ (False ∨ False)) ∧ False)))) → (True ∨ True)))) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
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
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744816548475400625742889241388 : ((((p3 ∧ p3) → ((p2 ∧ (False ∨ (p1 ∨ ((False → p1) ∧ (p2 ∧ p3))))) ∨ (True → (p5 ∨ ((p1 ∨ p1) ∧ (p5 ∨ (p4 → False))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39191966778331122055659787610 : ((((p5 → False) → ((p2 ∧ (p3 ∨ ((True ∨ False) ∧ ((((((p4 → p4) ∨ p3) → False) ∧ p2) ∧ p3) ∧ (p2 ∨ p2))))) ∧ p2)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327090803152052369402169615768 : (True → (((p2 ∧ (p1 → p2)) → ((p4 ∨ p3) ∨ (((p3 ∧ ((p4 ∨ p3) ∨ ((False → (True → (True → p1))) → p2))) ∧ p3) ∧ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38214520145892060052233275488 : (((((p2 → (((p2 → p3) ∧ False) ∧ True)) ∨ (p4 → (((p5 ∨ p4) ∧ True) → ((p1 ∨ True) → False)))) → ((p5 ∧ p4) → p3)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655514144784461244195441477530 : ((((((p1 ∨ ((p3 ∨ True) ∨ ((p3 ∧ ((p5 → (p5 ∧ p4)) ∨ (p5 → True))) ∨ (p2 → p1)))) ∨ p4) → (True ∧ p4)) ∨ (p1 ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_14749481386923469610416136774 : ((((((((True ∨ (True ∨ p2)) → (p1 → p4)) ∧ (p3 → p2)) → (p2 → (p3 ∨ False))) ∨ p2) ∨ ((False ∨ True) ∨ p1)) ∨ (p2 ∨ True)) ∧ True) := by
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
theorem thm_5_vars_252633263566950565622913306636 : ((p5 → p4) ∨ ((p1 ∨ ((((p1 → p5) ∧ p3) ∨ ((False ∨ p3) ∨ ((p3 → (p2 ∧ p2)) ∨ (True ∨ ((False → p4) ∧ p3))))) ∨ p1)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748265246208416413123076995593 : ((((p2 → False) → ((((p1 → p2) → (((False ∧ ((p1 ∨ (p2 ∧ p3)) → (p2 → p3))) → p3) ∨ ((p4 → p5) → p1))) → p3) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_313841612183237851768329547828 : (p3 ∨ ((((p4 ∧ (p1 ∧ p5)) ∧ ((p2 ∨ (p5 ∨ p4)) ∧ ((((p5 ∨ p3) → p5) → False) ∧ (p2 → p2)))) → (p2 ∧ False)) ∧ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h9.left
      let h16 := h9.right
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h17 : ((p5 ∨ p3) → p5) := by
        -- Implications on the right can always be decomposed.
        intro h18
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h20 =>
          -- One of the premise coincides with the conclusion.
          exact h14
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h21 := h15 h17
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h9.left
      let h24 := h9.right
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h25 : ((p5 ∨ p3) → p5) := by
        -- Implications on the right can always be decomposed.
        intro h26
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- One of the premise coincides with the conclusion.
          exact h27
        case inr h28 =>
          -- One of the premise coincides with the conclusion.
          exact h7
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h29 := h23 h25
      -- False on the left can always be used.
      apply False.elim h29
  -- Conjunctions on the left can always be decomposed.
  let h30 := h1.left
  let h31 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h32 := h30.left
  let h33 := h30.right
  -- Conjunctions on the left can always be decomposed.
  let h34 := h33.left
  let h35 := h33.right
  -- Conjunctions on the left can always be decomposed.
  let h36 := h31.left
  let h37 := h31.right
  -- Disjunctions on the left can always be decomposed.
  cases h36
  case inl h38 =>
    -- Conjunctions on the left can always be decomposed.
    let h39 := h37.left
    let h40 := h37.right
    -- We want to use the implication h39 based on <expert-advice>. So we show its premise.
    have h41 : ((p5 ∨ p3) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h42
      -- Disjunctions on the left can always be decomposed.
      cases h42
      case inl h43 =>
        -- One of the premise coincides with the conclusion.
        exact h43
      case inr h44 =>
        -- One of the premise coincides with the conclusion.
        exact h35
    -- We have shown the premise of h39, we can now drive its conclusion.
    let h45 := h39 h41
    -- False on the left can always be used.
    apply False.elim h45
  case inr h46 =>
    -- Disjunctions on the left can always be decomposed.
    cases h46
    case inl h47 =>
      -- Conjunctions on the left can always be decomposed.
      let h48 := h37.left
      let h49 := h37.right
      -- We want to use the implication h48 based on <expert-advice>. So we show its premise.
      have h50 : ((p5 ∨ p3) → p5) := by
        -- Implications on the right can always be decomposed.
        intro h51
        -- Disjunctions on the left can always be decomposed.
        cases h51
        case inl h52 =>
          -- One of the premise coincides with the conclusion.
          exact h52
        case inr h53 =>
          -- One of the premise coincides with the conclusion.
          exact h47
      -- We have shown the premise of h48, we can now drive its conclusion.
      let h54 := h48 h50
      -- False on the left can always be used.
      apply False.elim h54
    case inr h55 =>
      -- Conjunctions on the left can always be decomposed.
      let h56 := h37.left
      let h57 := h37.right
      -- We want to use the implication h56 based on <expert-advice>. So we show its premise.
      have h58 : ((p5 ∨ p3) → p5) := by
        -- Implications on the right can always be decomposed.
        intro h59
        -- Disjunctions on the left can always be decomposed.
        cases h59
        case inl h60 =>
          -- One of the premise coincides with the conclusion.
          exact h60
        case inr h61 =>
          -- One of the premise coincides with the conclusion.
          exact h35
      -- We have shown the premise of h56, we can now drive its conclusion.
      let h62 := h56 h58
      -- False on the left can always be used.
      apply False.elim h62
  -- Implications on the right can always be decomposed.
  intro h63
  -- One of the premise coincides with the conclusion.
  exact h63



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248027259527333148905913846377 : ((p1 ∨ p5) ∨ ((p3 ∨ (((False ∨ p5) → ((p1 ∨ (((p5 → (p3 → (p2 ∨ True))) ∧ (p3 ∨ True)) → False)) ∨ p4)) ∨ True)) ∨ (p5 ∨ p2))) := by
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
theorem thm_5_vars_41537379735676496560960401750 : (((((((p3 → p5) → (p3 ∨ p4)) ∨ p5) ∧ (p1 ∨ p4)) ∨ ((((p4 ∧ p2) → (p4 → p5)) ∧ ((p4 → False) → p1)) ∧ True)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658558789713716905718760358534 : ((((p2 ∨ (p2 ∧ (p3 ∧ (p3 ∨ (((p4 → p5) ∨ (((False → p4) ∨ p4) ∨ p3)) ∧ (((p2 → p4) ∧ p4) ∨ p4)))))) ∨ (p5 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54073436422835824227218671427 : ((((p2 ∨ (p1 → True)) → (p5 → (p5 ∨ (p1 ∨ p5)))) → (((p2 ∨ (((p5 → True) → (p2 ∨ p4)) ∧ p1)) ∧ True) ∨ (p2 → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665280876147352776309292480816 : ((((((((p5 ∧ p2) ∧ p3) ∨ ((p1 → (p1 → p3)) ∨ p5)) → ((p4 → ((p5 ∨ p2) ∨ p5)) ∨ False)) ∧ p1) ∧ (False → (True ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193809928117094811414662889091 : ((p5 ∧ ((p3 ∨ ((p1 ∧ (True → p2)) ∨ p4)) ∨ p5)) → ((((p4 ∧ ((p1 ∧ p1) → (p2 → (p5 ∧ (p4 ∧ True))))) → p5) → False) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
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
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165142219564281230390326278616 : ((((p5 → (p5 ∧ ((p3 ∧ (p2 → False)) → ((True → p3) ∧ True)))) → p3) ∧ (p1 → False)) ∨ ((((p3 ∨ p1) ∨ p3) ∧ p4) → (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_383273065747448704585506774732 : (((((True → ((p1 → ((p1 ∨ (False → ((False ∨ ((p5 ∨ (p3 → p5)) ∨ p3)) → p4))) → p4)) ∧ (p2 ∨ (p1 → False)))) ∨ True) ∨ p2) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116715341209316815837278989534 : (((p2 ∧ False) ∨ ((True → ((p5 ∧ ((p1 ∧ True) → ((p4 ∨ ((True ∧ (p1 ∧ p5)) ∧ (p3 ∧ p2))) ∧ p1))) → p3)) ∨ True)) ∨ (False → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50682961970674584367105642108 : ((((((False ∧ p5) ∧ p3) ∨ False) → (((p2 ∨ ((((p2 ∧ p2) → False) ∨ p2) ∨ p5)) → p4) ∧ p3)) → (((True ∧ p2) → p3) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52146685848816254860937589194 : (((((p1 → p1) ∨ (p4 → (True ∨ ((p1 ∨ p5) ∧ (True ∧ p3))))) → (False → p2)) → ((p1 → (True ∨ False)) ∧ ((p1 ∧ p5) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164605833878332124079100705434 : (((False ∧ (((p5 ∧ (p1 ∧ p4)) ∨ True) → (p1 → (p2 ∧ (True ∧ (p2 → p1)))))) ∧ p3) ∨ ((p1 → True) → (p5 ∨ ((p2 → p5) ∨ True)))) := by
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
theorem thm_5_vars_592750513565023117322072024789 : ((((((((p1 ∨ ((p3 → (p1 ∨ (True ∧ p5))) ∧ (p2 ∧ p4))) ∧ (False → (p5 ∨ p5))) ∧ p4) → p5) ∧ (False ∧ (True ∨ True))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



