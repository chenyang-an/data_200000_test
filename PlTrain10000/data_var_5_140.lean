variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111304588983354142733364659831 : (((False ∧ ((((True ∨ ((p5 ∨ p2) → ((p5 ∧ p4) ∧ False))) ∧ p5) → (p2 → ((p1 → (p1 ∧ p1)) ∧ p4))) → p1)) ∧ True) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346309108545489776955889750227 : (p3 → ((((p3 ∨ p1) ∧ (p3 → ((p1 → (p5 ∧ p1)) ∧ ((p1 ∧ ((p4 ∧ (True → p2)) → (p3 ∧ p1))) → p2)))) → p5) ∨ (p2 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260486724810256063675831154199 : ((p3 → False) → (((True → (p2 ∨ (p4 → (False → False)))) ∧ ((False → p1) ∧ p5)) ∨ (((p5 ∧ (False ∧ p1)) ∨ (p5 ∧ True)) ∨ (False → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199057318029832285918809926920 : ((((p5 ∨ ((p3 ∧ p1) ∨ p3)) ∨ p1) ∧ p2) → (True ∧ ((p5 ∨ p5) → (p3 → ((True ∨ p1) → ((False ∨ p1) ∨ (p4 → (True ∧ p5)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h1.left
      let h8 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h11
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Conjunctions on the left can always be decomposed.
            let h14 := h13.left
            let h15 := h13.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h15
          case inr h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h17
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- One of the premise coincides with the conclusion.
            exact h6
      case inr h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h1.left
      let h21 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h24
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h23
        case inr h25 =>
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h26 =>
            -- Conjunctions on the left can always be decomposed.
            let h27 := h26.left
            let h28 := h26.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h28
          case inr h29 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h30
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- One of the premise coincides with the conclusion.
            exact h19
      case inr h31 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h31
  case inr h32 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h1.left
      let h35 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h36 =>
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h37 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h32
        case inr h38 =>
          -- Disjunctions on the left can always be decomposed.
          cases h38
          case inl h39 =>
            -- Conjunctions on the left can always be decomposed.
            let h40 := h39.left
            let h41 := h39.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h41
          case inr h42 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h32
      case inr h43 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h43
    case inr h44 =>
      -- Conjunctions on the left can always be decomposed.
      let h45 := h1.left
      let h46 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h45
      case inl h47 =>
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h48 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h32
        case inr h49 =>
          -- Disjunctions on the left can always be decomposed.
          cases h49
          case inl h50 =>
            -- Conjunctions on the left can always be decomposed.
            let h51 := h50.left
            let h52 := h50.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h52
          case inr h53 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h32
      case inr h54 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h54



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303772599737234084206125650351 : (p1 ∨ (((False ∧ ((((((p5 ∨ p1) ∨ p1) ∧ p5) → (p2 ∧ p5)) → (((False ∨ p5) → p1) ∧ False)) → (False ∨ (p2 → p1)))) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168920458933418435976950361655 : ((p5 ∨ (False → (p1 ∨ ((p1 → p1) ∧ (((p3 → p2) ∨ p1) ∨ ((p1 ∨ False) ∨ p4)))))) → ((True → (p5 ∨ p4)) ∨ ((p2 → p3) ∨ True))) := by
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
theorem thm_5_vars_179236517222226241422301379512 : ((p5 ∧ ((p5 → (((p1 ∧ False) ∨ p5) ∧ ((p1 ∧ p3) ∨ p1))) ∧ p3)) ∨ (((False ∨ False) → True) ∧ ((p4 → (p3 → (False → True))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345477209696800425849511746644 : (p3 → (((((((True ∧ (p5 → True)) ∨ True) ∧ (p5 ∨ (p1 ∨ (True ∧ p5)))) → (False → p3)) ∨ (p2 ∨ p2)) → ((p4 ∧ p4) ∨ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159023412497928878888884623126 : ((p4 ∨ (((True ∨ (p3 ∧ p2)) → p4) → (((p2 ∧ True) → (((p1 → p2) → p3) ∨ p2)) → p3))) ∨ ((p1 ∧ ((p5 ∨ p3) ∨ p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152526837892762725129333936270 : (((p4 → (p3 ∨ False)) ∨ ((((((False ∨ p4) ∧ p1) ∧ (p5 → p2)) → (True ∧ (p5 ∨ p4))) ∨ True) → p4)) → (p4 ∨ ((p3 ∧ False) ∨ True))) := by
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
theorem thm_5_vars_156691197278296732337657947485 : ((((((False → ((p5 ∧ False) → True)) ∧ (False → p1)) → (p1 ∧ True)) ∧ (p2 → (True → False))) ∧ False) ∨ (p5 ∨ ((p3 ∨ (p5 ∨ p3)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165991524537680256808255012394 : (((p2 ∧ p3) ∨ ((((p4 ∨ ((p1 → p1) ∧ p4)) → False) ∨ (True ∨ True)) ∨ (p2 ∧ p1))) ∨ (True → (p2 ∨ (((p2 ∨ False) → p1) ∨ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_180532899729271336312331697767 : (((((p4 ∧ (False ∨ p2)) → False) → (p1 ∨ p4)) ∨ ((p3 ∨ p2) → p3)) → ((((p4 → p3) ∧ True) → p2) ∨ (False → (p2 ∧ (p1 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_491515249771476316876745829735 : ((((((p1 ∨ p2) ∨ p3) ∨ False) ∨ (((((((True ∨ (p1 → True)) ∧ p2) ∧ p3) → False) ∧ ((p3 ∨ (p1 → False)) ∧ p5)) ∧ p2) ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_214158213778097146897929360561 : ((((p1 ∧ p4) → p5) → p5) ∨ ((((p1 ∧ (p4 ∧ (True ∨ (True → (False ∨ True))))) ∨ p4) ∨ ((p4 ∨ (p2 ∧ p3)) ∨ (p4 ∧ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43191687532833799198631912940 : (((((p1 ∨ True) → (((p1 ∧ (False ∧ (p3 ∧ p1))) ∧ p3) ∨ ((p4 ∨ ((False → (p4 ∧ True)) → p4)) ∧ (p3 → True)))) ∧ p5) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118703781777213575769979405939 : ((p5 ∨ ((((p2 ∨ p1) ∨ ((p1 ∧ ((((p5 ∧ p4) ∨ ((False ∨ p1) ∧ p1)) ∨ p3) → p5)) → p5)) ∧ (True ∧ p5)) → False)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137311299488110732128878497106 : ((p2 ∧ ((((p1 → (p3 ∨ p4)) ∨ (True → (p4 ∧ p1))) → p4) ∨ ((p4 ∧ p2) ∨ (p3 → (True ∨ (p2 ∨ p1)))))) ∨ ((p3 ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347411815710733894110889768544 : (p3 → ((((p3 → False) ∨ True) ∧ ((p4 ∨ p5) → p4)) → (((p2 ∧ True) → ((False → p3) ∧ p4)) ∨ (((p3 → False) → (p5 ∨ p5)) ∨ p2)))) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_919536017777420431763544314943 : (((((False → p4) → ((((p5 ∧ p3) ∨ ((p1 ∧ p2) → p1)) ∨ False) → p3)) ∧ (((p3 ∧ (((True ∨ p1) ∨ p1) ∨ True)) → p4) ∧ p5)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h6
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : (((p5 ∧ p3) ∨ ((p1 ∧ p2) → p1)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h13 := h8 h9
  -- One of the premise coincides with the conclusion.
  exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337516676962653381682432212856 : (p1 → (((((((p5 ∧ False) ∧ p1) ∨ p5) → ((p4 ∧ p3) ∨ (False → (p2 ∨ p3)))) → (p2 ∧ p1)) ∧ p3) ∨ (p5 ∨ (p2 ∨ (p1 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704860750243457538451856381281 : ((((p1 ∨ (False ∨ ((p1 → ((p1 ∧ p4) → False)) ∨ False))) → (((p2 ∨ p1) ∧ (p4 ∨ (False ∧ (False ∧ (False ∨ (p3 → p3)))))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89203865650823983814243702861 : ((((p5 → p5) → False) ∧ ((p1 ∨ (((p4 ∧ False) → ((((p4 ∧ (False ∨ p5)) ∨ True) → True) ∨ p5)) ∨ p2)) ∨ (True ∧ (p3 → True)))) → p3) := by
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
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : (p5 → p5) := by
        -- Implications on the right can always be decomposed.
        intro h7
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h6
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h11 : (p5 → p5) := by
          -- Implications on the right can always be decomposed.
          intro h12
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h13 := h2 h11
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h15 : (p5 → p5) := by
          -- Implications on the right can always be decomposed.
          intro h16
          -- One of the premise coincides with the conclusion.
          exact h16
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h17 := h2 h15
        -- False on the left can always be used.
        apply False.elim h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h21 : (p5 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h22
      -- One of the premise coincides with the conclusion.
      exact h22
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h23 := h2 h21
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67600928986783957187297220237 : ((p1 → (p1 ∧ ((p5 ∧ ((((p5 → ((p3 ∧ (p1 ∧ p2)) ∨ p1)) → p1) → False) ∨ (False ∨ ((p1 ∧ (False → p4)) ∧ p3)))) ∨ p1))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155418135245534726302655418493 : (((((p3 → p2) ∨ p2) ∨ p3) → ((p5 ∧ (p4 ∧ (p4 ∨ True))) ∨ (True ∨ ((True ∧ True) ∨ p4)))) ∧ (True ∨ ((p1 ∧ (False → p2)) ∧ p5))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112446538265370146091227659616 : (((((p5 ∧ (((False ∧ p5) → ((True → ((p2 → (False → (True ∧ p1))) ∧ (p3 ∨ False))) ∨ p1)) → p5)) → False) ∨ p1) → p3) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622264349331099284878824863548 : ((((p3 ∧ ((((((p5 → (((p2 ∨ (p2 ∧ True)) ∨ (((False → p1) ∧ False) → p5)) → p3)) ∧ p2) ∨ p1) → False) ∨ p3) ∧ True)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719506905933024228661273769116 : ((((p2 ∨ (p1 ∨ (True → False))) ∨ (p5 ∨ (p4 → (p2 ∨ (p3 → (p1 → ((((p5 → p2) ∨ p4) ∨ p4) ∨ (p3 ∧ (p3 ∧ True))))))))) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185008955429932535710595805500 : (((True ∨ p2) ∧ ((p2 ∧ p1) ∧ (p1 ∨ (True ∨ (p2 ∧ True))))) ∨ ((((p4 → False) ∨ p4) → (p1 ∨ ((p1 → p5) → True))) ∨ (p3 ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113494395456664813188603025987 : ((((p5 ∨ ((((p1 → True) ∧ ((p4 ∧ (p3 ∧ (False ∧ p1))) ∧ False)) ∨ p1) ∨ p3)) ∧ ((p4 ∨ False) → p3)) ∨ (p2 → True)) ∨ (p1 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300956230930641585261777468482 : (False ∨ (((((((p2 → (p2 → False)) ∧ p3) → p4) ∧ False) ∨ p5) ∨ False) ∨ (((True → (p3 ∨ ((p5 ∧ p1) → p5))) ∧ p5) → (True ∨ p2)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121532337642440720778409735817 : ((((((p1 ∧ (((((p3 → (p5 ∧ p3)) ∧ p5) → p2) → p5) ∨ (p5 → False))) ∨ (True ∨ p5)) ∨ False) ∨ (p5 → p2)) → False) → (p2 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((((p1 ∧ (((((p3 → (p5 ∧ p3)) ∧ p5) → p2) → p5) ∨ (p5 → False))) ∨ (True ∨ p5)) ∨ False) ∨ (p5 → p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677634196532191114325361003913 : (((((((((False → p4) ∧ p4) ∨ p1) → (p1 → ((False ∨ ((p3 ∨ p4) → p3)) ∨ p5))) → True) → p5) ∨ ((p2 → (True ∨ p3)) ∨ p1)) ∨ p4) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40921768865646552803281401310 : ((((p2 → ((((p3 ∨ (p4 ∨ p2)) ∧ p3) → (p1 ∧ (p2 → p1))) → ((p3 ∧ (p1 → (p1 ∨ False))) ∧ p3))) ∧ (p5 ∧ p3)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198044045110708853617490588781 : (((p2 ∧ p3) ∨ ((p5 → p2) ∧ (p5 ∧ p5))) ∨ (((((((False ∧ True) ∧ p1) ∧ p3) ∨ p1) ∧ True) ∨ p5) → (False → (p1 ∨ (p2 → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259390679891220908287916047032 : ((False → p3) → (((p3 ∨ (True → (p3 ∧ (p2 ∧ (((p3 ∨ p5) ∨ (p2 ∧ p1)) ∧ p4))))) ∨ p1) ∨ (((p2 → p1) → (p3 ∨ True)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51211685740335509004688425131 : ((((p2 ∨ (((False ∧ p4) → (p3 ∨ p5)) → p2)) ∨ ((False ∧ p1) ∨ ((p4 ∧ p2) ∨ p5))) ∨ (False → (p5 ∧ (p2 ∨ (p4 ∧ True))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_633209236357297696710772737915 : (((((p4 ∨ ((p5 → ((True ∨ p2) → ((p4 → (p3 ∨ p4)) → (p5 ∧ (p4 → False))))) ∨ (p5 ∧ (False ∧ p1)))) ∧ (p5 ∨ p4)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49306098761015435474003041939 : (((p1 ∨ ((p2 ∧ ((p3 ∨ ((p4 ∧ ((p3 ∧ (True → p5)) ∧ False)) ∧ True)) ∨ (False ∧ p4))) ∨ (p2 ∨ False))) ∨ (p5 ∨ (True ∨ p4))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234495123578674745131157025692 : ((p2 → (p5 ∨ p4)) → ((p5 ∧ (True → p2)) → (((((p1 → p5) → (p1 ∧ False)) ∨ (p3 ∧ ((False ∨ p3) ∧ p3))) ∨ (p5 ∨ p5)) ∨ p2))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165951178398153629029679479657 : (((p3 ∨ p5) ∧ (((p1 ∧ p1) ∨ True) → ((((True ∧ (p5 ∧ p3)) ∧ False) ∧ p3) ∨ p5))) ∨ ((False ∧ (False ∨ p2)) → ((p4 ∧ p3) ∨ True))) := by
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
theorem thm_5_vars_958075878002512551189995990434 : ((((False → (p4 ∨ False)) → ((((False ∨ (True → (p1 ∨ p2))) ∧ ((p4 ∨ p4) → (p5 ∧ (((p1 ∧ p5) ∨ True) → p2)))) → p2) ∧ p4)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (p4 ∨ False)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319916767528572146571719273973 : (p4 ∨ (((p2 ∨ False) ∧ (p1 → False)) → ((((((False ∨ (True → p1)) → (True → p1)) ∨ (p4 ∨ (p3 → (p4 ∧ False)))) ∨ False) → False) ∨ p2))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306402932594130000876241943766 : (p1 ∨ ((p1 ∧ False) ∨ (((p1 ∧ (((p5 → p2) → (False ∧ p1)) ∨ ((p3 ∧ False) → p5))) ∧ (((False ∧ True) → True) ∧ p5)) → (p3 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141483309720474544517878284617 : (((p4 ∨ (p1 ∨ p4)) ∧ (((p1 ∨ (((p2 ∨ ((p1 ∨ p5) ∨ False)) ∨ p5) ∧ p3)) → p3) ∨ ((False ∧ p3) ∨ p3))) → (p1 ∨ (False ∨ p4))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- False on the left can always be used.
        apply False.elim h8
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- False on the left can always be used.
          apply False.elim h16
        case inr h18 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- False on the left can always be used.
          apply False.elim h23
        case inr h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143326623379066768778958764666 : ((p4 → ((((p3 ∨ True) ∨ p5) ∧ ((True ∧ (p5 ∨ (False ∨ True))) ∧ p1)) ∧ ((p4 ∨ p3) ∧ (p4 → (False → False))))) → ((p4 ∨ p1) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116186254322158659903287746579 : (((p5 → (p5 ∨ p3)) ∧ (p3 → (((((False ∨ False) ∨ (True → (p2 ∨ p2))) → (((p5 ∧ p4) ∨ p3) → p5)) ∨ p1) ∨ p2))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54498122922241818319417126804 : ((((p3 ∧ (True ∧ p1)) ∧ ((p4 ∧ p1) ∨ p3)) ∨ (p4 → ((((p2 → (p3 → p4)) ∧ False) ∨ (p1 ∧ p1)) → ((p4 ∧ p1) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112183602066410465827961681089 : (((p4 ∧ (p5 → ((p3 ∨ (((p5 ∧ p4) ∧ (True → (p2 ∨ p3))) → (((False ∨ False) ∧ (p1 ∨ p1)) ∧ True))) ∨ True))) ∨ True) ∨ (p5 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306061533500837454814802554216 : (p1 ∨ ((p5 ∧ (True → (p2 ∧ True))) → ((p3 ∧ (((p4 → p3) ∧ p3) ∨ True)) ∨ (p1 ∨ (p1 → ((p5 ∨ (p1 → (p3 ∨ p2))) ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51877116674507501679419755746 : ((((p5 ∨ ((p4 → (p1 ∨ False)) → (p5 ∧ ((p1 ∨ False) → (p2 → p3))))) ∨ p5) ∨ ((p4 ∨ (p3 ∨ p3)) ∨ (p5 ∨ (True ∨ False)))) ∨ p2) := by
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
theorem thm_5_vars_677876994178842252440580577902 : ((((((((p3 ∧ p5) ∨ ((False → True) ∧ True)) ∨ ((p2 ∨ p1) → (p1 ∧ p2))) → p4) ∨ (p2 ∨ True)) ∨ ((p3 → p3) ∧ (p4 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172232906009298158310777863921 : (((((p5 ∧ p4) ∧ ((p4 ∧ p3) ∧ p3)) ∨ p1) ∧ (p2 ∨ (p4 → (True → p2)))) ∨ (((True → (p2 ∧ p1)) ∨ (p5 → (p3 → p3))) ∨ p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115259474426008193156325919308 : ((((p5 ∧ p3) ∧ (True → (p3 ∨ ((p4 ∨ p1) → True)))) ∨ ((p4 → True) ∧ (((p1 ∨ p2) ∧ (p4 → True)) ∧ (p1 ∧ p3)))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160792979132704925700317631729 : (((((p5 → p2) ∨ True) ∧ (False → p1)) ∨ ((((p3 → (False → p1)) → (p2 ∧ p4)) ∧ p2) → True)) → (p1 → (p2 → (p1 ∧ (True ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174955700216832238049307971119 : ((True ∧ ((p4 → (p3 ∨ ((p4 ∨ (True ∨ (p4 ∧ False))) → (p5 ∨ p5)))) → p2)) → (((True ∧ ((True ∨ p2) → (False ∧ True))) ∧ p5) → p4)) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h9 : (True ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h10 := h6 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729882040494820094888731628330 : (((((p2 ∧ True) → True) → ((p1 ∨ (((((((False ∨ p3) ∧ p2) ∧ p1) → False) ∨ p4) ∧ p4) ∧ p2)) → (p4 → (False ∨ (p1 → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184590254334217539382816320681 : (((p5 ∨ (((p2 ∨ p5) ∨ (p1 ∧ p2)) → p4)) → (p5 ∨ p1)) ∨ ((((False ∨ (False ∧ (True ∧ False))) → False) → (p5 ∨ (p1 ∧ p2))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312005495397764422487441495639 : (p2 ∨ (p4 ∨ ((((p4 ∨ p1) ∨ (((False ∧ p1) ∨ p4) → p1)) ∧ ((p5 ∨ (True ∨ p2)) ∨ p3)) ∨ ((p3 → False) → (p3 → (True → p1)))))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351684175918627168762858429169 : (p4 → ((True → ((((p1 → p4) ∧ p4) ∧ (p2 → (p3 → p5))) → (p3 → (p3 ∧ p2)))) → ((p5 → p1) ∨ (p4 ∧ (p1 ∨ (p5 → p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214534590104493887099773759159 : (((True ∨ True) ∧ (True → p5)) ∨ (((p1 → (False ∨ ((p5 ∨ (p2 ∧ p3)) → ((p4 → (p4 ∧ p2)) ∨ True)))) → (p5 ∧ False)) → (True → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p1 → (False ∨ ((p5 ∨ (p2 ∧ p3)) → ((p4 → (p4 ∧ p2)) ∨ True)))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h3
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44176076947331856028352627126 : ((((p2 ∧ (p3 ∧ (True ∨ (((True → True) ∨ p5) ∨ (((((p2 → True) ∧ False) → p5) → p5) ∧ p3))))) → (p1 ∨ (False → p3))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307351662741300528031198466451 : (p1 ∨ (p3 ∨ (p1 → ((p1 → (((((p5 → p5) ∨ False) → False) ∧ (True → (((True → p3) ∧ p1) → False))) → ((False ∨ p5) ∨ p5))) ∨ p5)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((p5 → p5) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178670261446323931023789516488 : (((p1 ∧ (p2 ∨ (p3 ∧ p3))) ∧ ((((True ∧ p3) → p5) ∧ p4) → p3)) ∨ (True → ((True ∧ True) ∧ ((False → p3) ∧ ((False ∨ p1) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118885003837637621255568198834 : ((True → (p1 ∧ (((p2 ∧ (((p3 ∧ (p5 → ((p4 → p3) → p2))) → p5) ∨ (False → (False ∧ (p3 ∨ p1))))) ∨ p1) → p3))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119250377749362974577971672373 : ((p2 → (p1 ∨ ((True ∨ ((((p1 ∨ False) → (p4 ∧ p3)) → ((p2 ∨ False) ∨ p3)) ∧ (p4 ∨ ((False → p2) ∧ p1)))) → p1))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47093602348139203338430919037 : ((((p2 ∨ (p2 ∧ ((((p2 → p5) ∨ p4) ∧ (True ∧ (p1 → p4))) ∧ (p2 → (False ∨ (False → p2)))))) → (p4 → p3)) ∨ (p2 ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317093881251650789501440178561 : (p3 ∨ (p5 → (((((False ∧ ((p2 ∨ (p1 ∧ p3)) ∨ True)) ∧ p4) ∨ ((p3 ∨ p1) ∧ (((True ∧ p5) ∧ (p4 ∧ True)) → p2))) ∨ p4) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247818220208983095606974945331 : ((p1 ∨ p1) ∨ (p4 ∨ (((True ∨ (p2 ∨ ((True → p5) → (p4 ∨ True)))) → ((((True ∧ (p5 → (p2 ∧ False))) → p5) ∧ True) ∧ False)) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p2 ∨ ((True → p5) → (p4 ∨ True)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693820284809812006848006128046 : ((((((((p2 ∧ p2) ∧ p5) ∧ (True ∧ True)) → ((p4 ∧ p3) → p1)) → p5) ∨ (((p3 ∨ (True → False)) ∧ (p1 ∧ p4)) → (False → p1))) ∨ p5) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733955510862181817871898926102 : ((((True ∨ False) ∧ ((p5 → ((False → True) → p5)) ∧ (False ∨ (((p5 ∧ (((p2 → p3) ∧ p4) → p2)) ∧ (p5 → (p4 → p2))) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809344664811356737650341890450 : (((p5 → ((False ∨ (p3 ∧ ((p1 ∨ (False ∨ False)) ∧ ((((True ∧ p5) ∨ ((False ∨ False) ∧ (p5 → False))) → (p2 ∨ p3)) ∧ p1)))) ∨ p5)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50190920269766402341395291363 : ((((True ∧ ((p2 ∨ (((p4 ∧ (p5 ∧ (p2 → False))) ∧ (False → (p3 ∧ p2))) ∧ p1)) ∨ True)) ∧ p2) ∨ (p4 ∨ (False → (p1 → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135768525110718295344553641780 : (((((p1 ∧ (p2 ∨ (((p5 ∨ p2) → False) ∨ p4))) → (p5 → p3)) ∧ p5) → ((p5 ∧ (False ∨ (p5 ∧ p2))) ∨ p3)) ∨ ((p2 ∧ p1) → p2)) := by
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
theorem thm_5_vars_178404415805254317029819358951 : ((((p1 ∨ False) ∨ ((p5 ∨ p2) → ((False ∨ p3) ∧ p3))) → (p1 ∨ p4)) ∨ (False → ((((False ∨ (p3 ∨ p4)) → p5) → p3) → (p5 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774860488052819687267684838742 : (((False ∨ (((p1 ∧ (p4 ∧ True)) ∨ p3) ∨ (((p3 ∨ False) → p5) ∨ ((p4 ∨ (False ∧ ((False ∨ True) ∨ (p1 ∧ p5)))) ∨ (True ∨ p3))))) ∨ False) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9653979628182302562048005512 : ((((p5 → p3) ∧ ((p2 ∧ p4) ∨ (((p2 ∧ ((p2 ∧ p2) ∧ True)) ∨ False) ∧ ((p5 → (p4 ∧ p1)) ∨ ((True → p3) ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691660171895053718571473530719 : ((((p5 ∧ ((((p5 ∧ ((True → p1) ∧ p4)) ∨ False) ∨ ((p4 ∨ p1) → p3)) → True)) → ((p5 ∨ ((p3 → p2) ∧ (True ∨ True))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161714452911457991084286150617 : ((p3 ∨ (((p2 ∨ False) ∨ ((p4 ∨ p5) ∧ (p5 → ((p2 → (False ∨ (p1 → p4))) → False)))) ∧ True)) → ((p5 ∨ ((False ∧ True) ∨ True)) ∨ p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
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
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137746908461423969332056289147 : ((p2 ∨ ((p2 ∧ ((True ∧ p3) ∨ ((True ∨ (((p5 ∧ (True → p5)) ∧ (p3 ∨ p5)) ∨ (p3 → p1))) → False))) ∧ True)) ∨ (False → (True ∧ p2))) := by
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
theorem thm_5_vars_167889245397405624996319637119 : (((p3 → (False → (p2 → ((p5 ∧ p1) → (True ∧ True))))) → ((p5 ∧ p1) ∧ (p2 ∨ p3))) → (p4 ∨ ((p1 → p2) → (p3 ∨ (p1 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p3 → (False → (p2 → ((p5 ∧ p1) → (True ∧ True))))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h3
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_899406909025086725084263012690 : ((((((p1 ∨ p5) → (((p2 ∨ p3) ∨ True) ∧ (p3 ∧ (p1 ∧ ((p2 ∧ p4) → True))))) ∨ (True ∨ (True ∧ True))) → (False ∨ (False ∧ p5))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ p5) → (((p2 ∨ p3) ∨ True) ∧ (p3 ∧ (p1 ∧ ((p2 ∧ p4) → True))))) ∨ (True ∨ (True ∧ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56235991195573010859577176182 : (((p5 ∨ ((p5 ∧ p3) ∨ False)) ∨ ((p4 ∧ ((p3 ∧ p3) → (True ∧ (((p2 ∨ ((p5 → p4) ∨ p1)) ∧ (p1 → p5)) ∨ True)))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184893439446765085686652362064 : (((p3 → (p5 ∨ True)) ∧ (((p1 ∧ p4) ∨ p4) ∨ (p4 ∧ p1))) ∨ (((p5 ∧ p2) ∧ (True ∨ True)) → (p1 → (p3 ∨ ((p4 ∧ p4) → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171404770231581860221330056142 : ((((((False ∧ p4) → p1) ∨ p2) → (((True ∨ (p4 → False)) → False) ∨ p2)) ∧ p2) ∨ ((p1 ∧ ((p2 ∨ False) ∧ ((p1 → p2) ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191261402036067627606743365909 : (((p5 ∧ False) ∧ ((p4 ∧ ((p2 ∨ p4) ∧ p4)) → True)) ∨ (((p5 ∧ False) ∧ ((p4 ∧ ((p1 → ((p4 → p2) ∧ p5)) ∧ p4)) → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56238127910764204865075268801 : (((p5 ∨ (p1 ∧ (p4 ∨ p3))) ∨ (p3 ∨ (((p5 → p1) → (((p1 → (p5 ∨ True)) → p3) → p1)) → (((p5 → False) ∧ p3) ∨ True)))) ∨ False) := by
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
theorem thm_5_vars_597349012651171403531563587016 : (((((p4 → ((p5 ∧ p1) ∧ p5)) ∧ (True → ((((True → p2) → (p3 ∨ p4)) → ((((p4 ∧ p4) ∨ True) ∨ p5) → p4)) ∨ False))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178922339596451860323508931061 : (((p2 → p4) ∧ ((((p3 ∧ p4) → p3) ∨ p2) ∨ ((p1 ∨ p2) → False))) ∨ ((True → p1) ∨ (p3 → ((p5 ∧ (p1 ∨ (False ∧ p2))) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8779088852219773856172302395 : ((((((p4 → ((p2 → (p1 ∧ (p2 → p3))) ∧ p2)) → (p5 → (p3 → False))) ∨ (p5 → (p3 → p5))) ∨ ((p3 ∨ p3) ∨ p3)) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172394502327470553308002083953 : ((((True → True) ∨ (False → (p5 ∧ False))) → ((p4 ∧ (True → p3)) ∧ (p3 ∨ True))) ∨ (True ∨ ((p2 → (p1 ∧ (p1 → False))) ∨ (p4 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39524623742101420705234058796 : (((False ∨ ((p3 ∨ ((((p5 ∨ p2) ∨ p4) ∧ ((p3 ∧ p2) ∨ False)) ∨ (((p3 ∨ True) ∧ True) → True))) ∧ (p5 → (True ∧ p3)))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66203855236912939967150040579 : ((p5 ∨ (((p4 ∨ ((((p4 → p4) → (p3 → (p1 ∧ p4))) ∨ False) ∨ p2)) ∧ p5) ∨ (((False ∨ ((False ∨ True) ∧ False)) → p5) ∨ True))) ∨ p1) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55406936060748688606605093518 : (((((False ∨ (True ∨ True)) ∨ p3) ∨ p1) → (((((True → (p1 → ((False → p4) ∨ False))) ∧ ((p4 → p5) → True)) ∧ True) ∧ p3) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327475848213804421050460742020 : (True → (((((False ∨ p4) → (p1 ∧ False)) ∧ p5) ∧ ((p4 ∨ (p5 → False)) ∧ ((p2 ∧ p1) ∨ ((p5 ∧ (p3 → p1)) ∧ (p5 → p5))))) → False)) := by
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
  let h7 := h4.left
  let h8 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h13 : (False ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h14 := h5 h13
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h21 : (False ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h22 := h5 h21
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- False on the left can always be used.
      apply False.elim h23
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h28 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h29 := h24 h28
      -- False on the left can always be used.
      apply False.elim h29
    case inr h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Conjunctions on the left can always be decomposed.
      let h33 := h31.left
      let h34 := h31.right
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h35 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h33
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h36 := h24 h35
      -- False on the left can always be used.
      apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717708418422992686785574508904 : ((((((p2 → p4) ∧ p1) ∧ True) ∨ ((p2 ∨ (False ∧ p1)) ∧ (False ∧ ((p4 → (True ∨ (p4 ∨ p5))) ∨ (p5 ∨ (p5 → (p2 ∧ p1))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151469533614639604546606413905 : (((((((p3 ∨ False) → (p5 ∧ p5)) ∨ p1) ∧ ((p3 ∨ ((p5 ∧ p5) ∨ p1)) → p4)) → p5) ∨ (p3 ∧ False)) → ((p3 ∧ p5) → (p2 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55809357543292466975515421201 : ((((p3 ∧ p1) → (False → p5)) ∧ ((p3 ∨ (p2 → ((p4 ∧ p4) ∧ (False → ((p1 → ((p1 → p5) ∨ (p2 → p5))) ∨ True))))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65757751648592474560771929833 : ((p4 ∨ (((((p1 → True) ∨ (p4 ∨ (p3 ∨ False))) ∨ p4) → (((True ∧ (p1 ∨ False)) → p4) ∨ False)) ∨ (p1 ∨ (p2 → (False ∨ True))))) ∨ p4) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668411769704257633728917304509 : (((((((p4 ∨ (((True ∧ p4) ∧ p3) ∨ (True → ((False → ((True ∨ p5) ∨ p1)) ∧ p4)))) → p5) ∨ p5) ∧ p4) ∨ ((p4 ∧ p4) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



