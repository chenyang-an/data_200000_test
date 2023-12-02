variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592430980507318510426113316547 : (((((((((p4 ∧ (p3 → p3)) → True) → p2) ∧ p3) → ((False ∨ ((p5 ∨ p2) ∨ ((p2 ∨ p1) ∨ p5))) ∧ False)) → (True ∧ p3)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687981074578985414864148667183 : ((((((((p4 ∨ p1) ∨ p4) ∨ p5) ∧ p1) ∧ (((False ∧ False) ∧ True) ∨ (p4 → p2))) ∧ ((((p4 ∧ p5) ∨ True) ∧ (p3 → False)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148654093819491500796062150471 : ((((False ∨ p1) ∧ ((p5 ∧ p5) ∧ (p2 → p3))) ∧ (p1 → ((p3 → p2) → (((p1 → False) ∨ True) → p5)))) ∨ (False → ((p2 → p5) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350503452204369804236551630186 : (p4 → ((((((p5 ∨ p1) ∧ p3) ∧ (p4 → (p3 ∨ (((True ∧ (p2 → (p3 → False))) → p3) → p3)))) ∨ (p4 ∨ False)) → (False ∧ p3)) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((p5 ∨ p1) ∧ p3) ∧ (p4 → (p3 ∨ (((True ∧ (p2 → (p3 → False))) → p3) → p3)))) ∨ (p4 ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137489548336132820548583420677 : ((p5 ∧ ((True → ((False ∨ ((False ∧ True) → (p2 → False))) → (p4 ∧ ((((p3 → False) → True) → p5) → p4)))) ∨ True)) ∨ ((p4 ∧ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336235835977145118750526625660 : (p1 → (((((False ∨ (((False ∨ ((p3 ∧ p2) → p5)) ∨ (False ∧ True)) ∧ (p5 → p5))) ∨ p3) ∨ False) ∧ ((p3 ∨ (p2 ∧ False)) ∨ True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658346597144844824397457465532 : ((((False ∨ (((p5 → ((((p4 → ((p2 ∧ p2) ∧ True)) → (p5 ∨ p5)) → (p4 ∨ (p1 ∨ p5))) → False)) ∨ False) ∧ False)) ∨ (p2 ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_156668222153213760946880520660 : ((((((p3 ∨ (((p4 ∨ (p5 ∨ p5)) ∨ False) ∧ p5)) ∨ (p3 ∧ True)) ∨ p5) ∧ (p2 → p4)) ∧ p5) ∨ (p3 ∨ ((p1 ∧ p1) → (True → True)))) := by
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
theorem thm_5_vars_133656378791769957940662222041 : ((((((False ∧ (p5 ∨ p4)) → (((p3 ∨ True) → (False → (True ∧ p2))) ∧ (False ∨ p4))) → p2) ∨ (p1 ∨ p2)) ∧ p3) ∨ (p5 ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148670092919536489123630895053 : ((((p4 ∧ (p1 ∧ (p3 → (p2 ∧ p3)))) ∧ p4) ∨ (p5 ∨ (p5 ∨ ((False ∨ (p1 ∨ (p4 ∧ True))) → p5)))) ∨ (((p5 ∨ True) → False) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310042226389411388774186621995 : (p2 ∨ ((p1 ∨ (p5 ∨ (p2 ∧ ((p5 → p5) ∧ (p3 ∨ (p2 ∨ (False ∧ (p1 ∧ p4)))))))) ∨ (p3 → (p5 ∨ ((p3 → p3) ∨ (p4 ∧ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_776525214243332747605863080980 : (((p1 ∨ ((((p1 ∨ p4) ∧ (((p1 → False) ∨ True) ∧ False)) ∨ (((p5 ∧ False) → ((((p4 ∧ False) → p2) ∨ p2) ∨ p3)) → p5)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112104863801044601003276350308 : ((((False ∨ p4) → (((p5 ∨ False) ∧ (p4 → (p4 → ((p3 ∨ ((True ∨ p3) ∨ p2)) ∨ (p2 ∨ (p1 ∧ False)))))) ∨ False)) ∨ True) ∨ (p2 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57909364153826606936068026110 : (((p4 ∨ (False → p5)) → ((((p3 ∨ p5) → (p4 → p1)) → False) ∨ (True ∨ (True ∨ ((p5 ∨ p4) ∧ (False ∨ (p4 → (True ∨ p4)))))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232310850827946413140622521464 : (((p3 → p2) → p1) → ((((p4 → p2) ∨ (p3 ∨ (True ∧ p4))) ∧ False) ∨ ((p1 ∧ False) ∨ ((p4 ∧ ((p1 ∨ p4) ∧ (True → p2))) → p2)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h12 := h6 h11
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586546276198350426132013632443 : ((((((p2 ∨ p2) ∧ (((p2 ∧ (p2 ∨ (((p3 → ((p5 ∨ False) ∨ p4)) → p5) → p1))) ∧ ((p5 → p1) ∨ p3)) ∧ False)) ∧ p4) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115286870445467134511530439293 : (((((p4 ∨ ((p1 ∨ (False → False)) → p2)) ∨ p1) ∧ p4) → (p1 → ((p2 ∧ (((False ∧ p1) → p1) ∧ p4)) → (False ∨ p2)))) ∨ (p5 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61056002083552238038247717634 : ((False ∧ ((p4 → ((((p4 → p5) ∨ (p3 ∧ p1)) ∧ (p2 ∧ ((((False ∧ False) ∧ p5) ∧ False) ∨ False))) → (p4 ∧ True))) → (p2 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134697486960811180402170151699 : ((((p5 ∨ (True → (p2 → True))) ∧ (((((p2 ∨ ((p4 → p2) ∧ False)) ∧ True) ∧ p4) → (p1 ∧ False)) ∧ p2)) → p1) ∨ (True ∨ (p1 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61499802013445913423919048884 : ((p1 ∧ ((p3 → ((False ∧ (p1 ∨ ((True ∧ ((p4 ∨ ((True → p5) → (False ∧ p2))) → False)) ∨ True))) ∨ False)) → ((p5 ∨ p5) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133474207831222727084100763273 : ((p5 → ((((True ∨ p4) → p3) ∧ (((p1 ∨ p5) → (p4 ∨ p2)) ∨ p1)) ∨ (((p5 ∨ False) ∨ p3) → (p5 ∨ p1)))) ∧ (True ∨ (p5 ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150590412523653099995329573866 : ((((p4 ∧ False) ∨ (p3 → (((p3 → False) ∧ (True → (False → p2))) ∧ (p1 ∧ (p5 ∧ (p2 ∧ p3)))))) ∧ p1) → ((p2 ∧ True) → (p2 ∧ p1))) := by
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
  let h5 := h1.left
  let h6 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- False on the left can always be used.
    apply False.elim h17
  case inr h18 =>
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133856459088870473976106301365 : (((p1 ∧ (((((p4 → p4) ∧ (((p4 → False) ∧ p2) ∨ p3)) ∧ ((p2 ∨ True) ∨ True)) ∧ p5) ∨ (False ∨ p4))) ∧ False) ∨ (True ∨ (p4 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120722352137083609991163408988 : ((((p4 ∨ (p3 ∨ (p5 ∨ (p2 ∨ ((((p4 ∨ p3) ∧ (False ∧ p4)) ∧ False) ∨ (p3 → (p3 ∨ p4))))))) ∨ (p1 ∨ p4)) ∨ True) → (p4 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
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
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h9 =>
            -- Disjunctions on the left can always be decomposed.
            cases h9
            case inl h10 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h11 =>
              -- Disjunctions on the left can always be decomposed.
              cases h11
              case inl h12 =>
                -- Conjunctions on the left can always be decomposed.
                let h13 := h12.left
                let h14 := h12.right
                -- Conjunctions on the left can always be decomposed.
                let h15 := h13.left
                let h16 := h13.right
                -- Disjunctions on the left can always be decomposed.
                cases h15
                case inl h17 =>
                  -- Conjunctions on the left can always be decomposed.
                  let h18 := h16.left
                  let h19 := h16.right
                  -- False on the left can always be used.
                  apply False.elim h18
                case inr h20 =>
                  -- Conjunctions on the left can always be decomposed.
                  let h21 := h16.left
                  let h22 := h16.right
                  -- False on the left can always be used.
                  apply False.elim h21
              case inr h23 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h26 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h26
  case inr h27 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46492244875252926741596444532 : (((((p2 → p5) ∧ p4) → (((((True ∧ (False ∨ p5)) ∨ ((True ∨ p1) ∧ False)) → p1) ∧ True) ∧ ((p3 ∨ p1) ∨ p4))) ∧ (p3 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158439565437407643429164572085 : (((p2 ∨ p1) ∨ (((False → (p1 → (p3 ∧ (p5 → p4)))) → (True ∧ p1)) ∧ ((p3 ∧ False) ∨ p2))) ∨ ((((False → p5) ∨ p2) ∧ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179179892644674502288929481920 : ((p3 ∧ (((p3 ∧ p5) ∨ (((p4 ∧ (p1 ∧ p1)) ∧ False) ∨ False)) ∨ p1)) ∨ ((True ∧ p3) → (((p2 ∧ p4) ∨ p1) ∨ (False → (p5 ∧ p1))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649210258084553746247478171976 : ((((((False → False) ∧ (True → ((True ∨ p1) → ((((False ∧ ((p3 → (p2 → p1)) ∧ False)) ∧ p2) → p3) → p4)))) → p2) ∧ (p4 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112109726953564079002028442882 : ((((p5 ∨ p1) → (p1 → (p1 → ((p3 ∨ p2) ∨ ((p1 ∨ p1) ∧ ((p1 ∧ ((p3 ∧ p5) ∨ p4)) → (False ∧ p4))))))) ∨ True) ∨ (p5 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209146883596362526636965591921 : ((p3 ∨ ((p2 → (p2 ∨ False)) → p2)) → (True → ((False ∨ (p5 ∨ p2)) ∨ ((p4 → ((p3 ∨ True) ∨ ((p2 ∨ (p5 ∨ False)) ∧ p1))) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p2 → (p2 ∨ False)) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146995300892596626607973083134 : (((((((p2 → ((((p4 ∨ (True → p4)) → p4) ∨ p4) ∧ True)) → p2) ∨ True) ∨ p3) ∧ (p2 ∨ True)) ∧ True) ∨ (((p4 ∧ p4) → p1) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632466082631113233085763158496 : (((((p2 ∨ ((p5 ∧ p1) ∨ ((False → p3) ∧ (p3 ∧ ((p2 → ((p3 ∧ False) ∧ p2)) → ((False ∨ (p1 ∧ p2)) ∧ p1)))))) → p2) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209562476483905015842131497398 : ((p5 → (((p1 → p2) ∧ False) → p5)) → ((True ∧ (False → p5)) → (((p5 → p5) ∧ (True ∧ ((True ∨ (p3 ∨ (p5 ∨ p4))) → p3))) → p3))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h10 : (True ∨ (p3 ∨ (p5 ∨ p4))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h11 := h7 h10
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68122831447624669594940498045 : ((p2 → (p4 → ((((False → (p3 ∨ (p4 ∨ p3))) ∧ p1) → ((p4 → ((True → (p1 ∨ True)) ∧ True)) → p5)) ∨ (p1 ∧ (True ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206177554257609766640258702084 : ((p5 ∧ (False ∧ (p4 ∨ (p1 ∧ False)))) ∨ (p1 → (((((False ∨ (p4 ∨ (True → p5))) ∧ p1) ∨ (p5 → p5)) ∧ ((False ∧ False) ∨ p1)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658496241549722819552080485749 : ((((p1 ∨ (p2 → (p1 ∨ (((p3 → (True → True)) → (p1 ∨ p3)) ∨ ((((p4 → (p3 → True)) ∧ p5) → False) ∨ p2))))) ∨ (p1 → True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349053520965741920376040129717 : (p3 → (p5 ∨ ((p3 ∧ (((p1 ∧ True) → (p3 → False)) ∧ (p2 → (False → p1)))) ∨ (((p5 ∨ (True ∧ p1)) ∨ (p1 ∨ p3)) ∨ (p4 ∨ p5))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51738651505000014283566467329 : ((((p1 ∨ (True ∧ p4)) ∧ ((False ∧ (((True ∨ True) → p4) ∧ (p4 ∨ p5))) ∨ p3)) ∧ ((p3 ∧ p3) → ((p5 → (p1 → p4)) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619659973874738522827069045252 : (((((p3 ∧ p3) ∧ (p4 ∨ (((p4 ∧ p2) ∨ (False ∨ ((False ∧ (((p4 ∧ (p3 → p4)) → p5) ∨ (False → p4))) ∧ True))) ∨ p1))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_206432657021713816897811429933 : ((p4 ∨ ((False ∨ (True → False)) ∧ p4)) ∨ ((True → (p3 ∨ (p4 ∨ p1))) ∨ ((p5 ∧ (((p5 → (False ∧ (p1 ∧ p2))) ∨ p1) ∧ p2)) → p5))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229155942248643840213223383979 : ((True → (p1 ∨ p1)) ∨ (((((p2 ∨ p5) → False) ∧ (p3 → ((p1 ∧ (p2 ∧ (False → p3))) ∨ (p3 → ((p5 ∧ p2) ∧ True))))) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218050491460551325587556030743 : (((p3 ∨ True) ∧ (p1 → False)) → (True → ((p2 ∨ ((p5 ∧ False) ∧ True)) ∨ ((((True ∨ p1) ∨ (p5 → p3)) ∨ (p4 ∨ p3)) → (False → p4))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302546412801057771449144655502 : (False ∨ (False ∨ (p1 → ((p1 ∧ (p4 ∨ (((((p2 ∨ False) ∧ (p2 ∧ p3)) ∧ (((p1 ∨ p5) → p3) ∧ p3)) ∧ p4) ∨ (True → False)))) ∨ True)))) := by
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
theorem thm_5_vars_646776409331732943147565462929 : ((((p2 → ((True → (p3 → ((p1 ∨ p5) → (True → (((p5 ∧ ((p4 → p2) ∨ p3)) ∧ p2) → p4))))) ∧ ((p1 ∨ p1) ∧ False))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56503816149273678792099795494 : (((p2 ∧ (False ∨ (p4 → p1))) → ((True ∧ p4) ∨ (((True → ((p4 ∨ p2) ∨ ((p2 → p1) → p2))) → ((p5 ∧ p1) ∨ p4)) ∨ p2))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_868299046160860242993131838890 : (((((p4 ∨ p2) → (((p2 ∧ p4) ∧ (((((p3 ∨ False) ∨ False) → p2) → (p5 → ((p3 → p1) ∧ (p2 → p3)))) → p5)) ∨ True)) → False) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∨ p2) → (((p2 ∧ p4) ∧ (((((p3 ∨ False) ∨ False) → p2) → (p5 → ((p3 → p1) ∧ (p2 → p3)))) → p5)) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68999571141245083182062934477 : ((p5 → ((((True → p5) ∧ ((p1 → (p5 ∨ p3)) → ((False → (p2 ∨ False)) → p4))) ∧ (p2 ∨ (((p3 ∨ p5) ∧ False) ∧ p1))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118679937500434326589667771271 : ((p5 ∨ (((((p3 ∧ ((((False ∨ True) ∧ p3) ∨ p2) ∧ p4)) ∨ p4) ∧ ((True ∨ ((p1 ∧ True) ∨ True)) ∧ False)) ∨ p5) ∧ p4)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180657891553251475287745483096 : (((p4 ∨ ((False ∧ (p2 → p2)) → p1)) ∨ (p4 ∧ (True ∧ (p2 → p4)))) → (p1 → (((p4 ∨ p4) → (p3 ∧ (p5 ∨ (p2 ∧ p2)))) ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87853562720578314145321933236 : (((((p1 ∨ p5) → p3) → (p5 → p5)) → (((p4 ∧ p2) ∧ ((((p3 ∨ False) ∧ (False ∨ True)) → True) ∧ p5)) ∧ (False ∨ (True ∨ p3)))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ p5) → p3) → (p5 → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89361382670910416954302230356 : (((True → (p4 ∧ p1)) ∧ ((((p1 → ((p5 ∨ (True ∨ p4)) ∨ (p1 → p2))) → True) ∨ (((p4 → p5) ∨ p3) ∨ p2)) ∨ (p2 ∧ p1))) → p1) := by
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
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- We need to get the right conjuct of h7 based on <expert-advice>.
      let h8 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h12 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h13 := h2 h12
          -- We need to get the right conjuct of h13 based on <expert-advice>.
          let h14 := h13.right
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h16 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h17 := h2 h16
          -- We need to get the right conjuct of h17 based on <expert-advice>.
          let h18 := h17.right
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h19 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h20 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h21 := h2 h20
        -- We need to get the right conjuct of h21 based on <expert-advice>.
        let h22 := h21.right
        -- One of the premise coincides with the conclusion.
        exact h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- One of the premise coincides with the conclusion.
    exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48993781346842127201232474114 : ((((p4 ∧ ((p1 ∨ ((False ∨ (False ∨ ((((p4 ∧ p5) → p4) → p4) ∨ True))) ∧ p3)) ∧ (True ∨ p3))) ∨ True) ∨ (p5 ∨ (p1 ∨ True))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20903803746326505504262304010 : ((((p3 → p1) → (False ∧ ((p2 ∨ (p1 ∨ (p1 → p5))) ∧ False))) ∨ (True ∨ ((True ∨ (p3 ∨ ((p4 → p1) ∨ (p4 ∨ p1)))) → p5))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356363402141027281933972686955 : (p5 → ((p4 ∧ (((p3 ∧ (((True ∨ p2) → False) ∨ (True → False))) ∧ p3) ∨ p1)) ∨ (True ∧ (((p5 ∧ ((True ∨ p3) → p1)) → p4) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63241632632536734632445702422 : ((p5 ∧ ((((p4 → p2) ∨ (p3 → p4)) ∧ (p4 ∨ ((p5 ∧ p5) ∧ p5))) → (False ∨ ((p4 ∨ p2) ∧ ((p1 ∧ False) ∨ (True ∨ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_442001455588098931793300631249 : (((((((p1 → False) → (((p2 ∧ p2) ∧ p1) ∧ p5)) → ((p5 → (((p3 ∨ p5) ∧ p1) ∧ p2)) ∧ p5)) ∧ p4) ∨ ((True → True) ∨ p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151899644124130658254655188885 : (((((p2 → False) → p5) → (True → (p1 ∨ ((p1 ∧ (p5 → True)) ∧ True)))) → (p2 ∨ ((True → p5) ∨ p1))) → (p5 → ((p1 ∧ False) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228830510203931731108310559520 : ((p3 ∨ (True → p1)) ∨ (p4 → ((((p5 ∨ p3) → p4) → False) ∨ (p5 → ((p4 → p5) → ((p4 → ((p4 ∧ p1) → (True ∨ p1))) → p5)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135347173792370555428122197772 : (((p1 ∧ (p3 ∨ (((p3 ∧ (p5 ∨ p3)) ∨ p4) → ((((p5 ∨ True) ∨ p3) ∨ p2) ∧ False)))) ∧ (True ∨ (p3 ∧ False))) ∨ (p1 → (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777607130319581251574860160843 : (((p1 ∨ (((p5 ∨ p3) → (((p4 ∧ (True ∨ p2)) → True) ∧ p5)) ∧ (((p2 ∧ (True → p4)) ∧ ((True ∨ p1) → p2)) ∧ (True → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615414730826186870947788383138 : (((((False ∨ (p2 ∨ ((p2 ∨ p4) → ((p3 ∨ (p4 ∧ p4)) ∧ (p4 ∧ (p1 ∧ p1)))))) ∨ (p5 ∨ (((True ∨ p3) → p4) ∨ True))) ∨ p1) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185249271152415646554525834722 : ((p1 ∧ ((((False ∨ p2) ∧ (p4 → (p4 ∨ False))) ∨ False) ∨ p4)) ∨ (p2 → (((p1 ∨ (False ∨ p1)) ∨ (p4 ∨ (True ∨ (p5 ∧ False)))) ∧ True))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154936067934673068224470618524 : (((p5 ∧ (((p5 → p1) ∧ (p4 → (p1 → ((p5 ∧ p2) ∨ p3)))) ∨ p4)) ∨ (p5 ∨ (p4 → p4))) ∧ (p4 → (p3 → (p3 ∧ (p5 → p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617872967211177061632510600513 : (((((((p4 ∧ p4) ∧ False) → (p4 ∨ p5)) → ((True ∧ p5) → ((p4 ∧ p3) ∧ (((p1 → (False → (False → p3))) ∨ False) ∨ p2)))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_230879221833379533105856966326 : (((p2 ∧ True) ∨ p4) → (((False ∨ ((p5 ∧ ((True → ((p1 ∨ p4) ∨ False)) ∨ (True → p4))) ∨ (p1 ∨ p5))) ∨ (p1 ∨ p1)) → (False ∨ True))) := by
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h10 =>
            -- Conjunctions on the left can always be decomposed.
            let h11 := h10.left
            let h12 := h10.right
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
          cases h1
          case inl h15 =>
            -- Conjunctions on the left can always be decomposed.
            let h16 := h15.left
            let h17 := h15.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h21 =>
            -- Conjunctions on the left can always be decomposed.
            let h22 := h21.left
            let h23 := h21.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h24 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h25 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h26 =>
            -- Conjunctions on the left can always be decomposed.
            let h27 := h26.left
            let h28 := h26.right
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
    cases h30
    case inl h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h32 =>
        -- Conjunctions on the left can always be decomposed.
        let h33 := h32.left
        let h34 := h32.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h35 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h36 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h37 =>
        -- Conjunctions on the left can always be decomposed.
        let h38 := h37.left
        let h39 := h37.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h40 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149504268853291185603188962106 : ((p1 ∧ ((p4 ∨ ((((p1 ∨ ((p1 ∧ p1) ∧ (p2 ∨ False))) → p1) ∨ p5) ∨ p4)) → ((False ∨ p1) ∧ False))) ∨ (p2 ∨ (False → (True ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_258747075697468749753611252207 : ((True → True) → (p1 ∨ (((((p1 ∨ p5) → False) ∧ (((False → False) ∨ p4) ∨ True)) ∨ ((True ∨ p3) → (False ∨ (p2 → (p3 → p2))))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106523973602049807214935338892 : ((((True ∨ (False ∨ False)) → (p3 ∧ (p1 → p3))) ∨ (p5 → ((((p4 → (p1 ∧ False)) ∨ (p2 ∧ (p2 ∧ p3))) → p4) ∨ True))) ∧ (False ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119173300615685458743834097169 : ((p2 → ((((p1 ∧ ((p5 ∨ True) → ((False → (p1 ∧ p4)) ∧ True))) ∨ (p4 ∨ (p4 ∨ (p1 ∨ (p3 → p2))))) ∧ p5) → p1)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172105082966074826252589829855 : (((True → (((False → p4) ∧ (((p5 ∨ p4) → p5) → p3)) ∨ False)) → (False ∧ p2)) ∨ ((((p4 → (True ∧ p2)) ∨ p2) → False) → (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142599466953285387409862252717 : ((False ∨ ((p1 → ((p2 ∧ (p1 ∨ (((False → True) → p1) ∨ p2))) ∧ False)) ∧ (p4 ∧ ((False ∨ (p2 → p1)) ∧ p2)))) → ((False ∨ p3) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h14 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h15 := h4 h14
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43441307331033149987013198095 : ((((((p1 ∧ True) ∧ p3) ∨ ((((False ∨ p4) → p2) ∨ p4) ∨ ((False → ((p3 ∧ (True ∨ (p4 → p1))) ∨ p1)) ∧ p5))) ∨ p3) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260223126266413417003895833359 : ((p2 → p3) → ((((p5 ∨ p3) → p2) ∧ (p4 → (p5 → (False ∧ ((p4 ∧ (((((p5 → p4) ∨ p5) ∨ p3) → p5) ∨ p3)) ∧ p4))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152122037830669632444625469989 : ((((p5 ∧ ((True ∧ False) ∨ p4)) → (p5 ∧ False)) ∧ ((p2 → ((p2 ∧ p1) ∨ True)) ∧ (p4 ∧ (p3 ∨ True)))) → (((True ∧ True) → p5) → p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : (True ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : (True ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h13
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118576143798109165769731759398 : ((p4 ∨ ((((p1 ∧ (((p3 ∧ p3) ∨ p2) ∨ (p4 → ((True → p3) → False)))) ∧ p5) → ((p2 ∧ (p5 ∨ p3)) ∧ p1)) ∨ True)) ∨ (True → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111014403125163974003343082531 : ((((p1 ∧ (((p2 ∧ p2) → (p2 ∧ (True ∨ (p2 → (((p3 ∧ p2) ∧ True) ∧ p4))))) → p4)) ∨ (p3 ∨ (p2 ∨ p1))) ∧ p1) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138338604167759831785108496145 : ((p4 → (((((((p4 ∧ p5) ∧ p5) ∧ ((p3 ∧ True) ∨ (p4 → ((p5 ∧ False) ∨ p5)))) ∧ False) → p2) → p3) ∧ p2)) ∨ (p3 → (p3 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599600390441370080666001533568 : (((((p5 ∨ p3) ∨ ((False ∧ True) ∨ (True → (((((p4 ∨ p3) ∨ (p4 → (True ∨ ((p2 ∧ False) ∨ p2)))) → p2) ∨ True) ∨ False)))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345418226346895468183089275313 : (p3 → ((((p4 ∨ p1) → (p4 ∨ ((((p3 → ((False ∧ p2) ∨ False)) → p5) → (p3 ∨ (p1 ∧ (p2 ∨ (p5 ∨ p5))))) ∧ p1))) → False) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775498743485939972602483786168 : (((False ∨ (p4 ∧ ((True ∨ (False ∨ (p5 → p1))) → (((p2 ∨ (p4 → ((True → True) → (p5 → p5)))) ∧ (p2 ∧ (True → p4))) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598462645785200425664314859756 : ((((((p2 ∧ p1) ∨ p2) → ((((True ∨ (p3 → p2)) → (True ∨ (p5 → (True ∨ True)))) → (p2 ∨ (p4 ∧ (p3 ∧ p1)))) → False)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156335013962991408134703750917 : ((True → (((p5 → (((p2 ∧ (False → p2)) → p3) ∧ (p3 ∧ True))) → (p4 ∧ (True ∧ p4))) ∨ True)) ∧ ((((p3 ∧ False) → p5) ∧ p4) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602867669193063885379208384 : (((p2 → (((p2 ∨ (p3 ∧ ((True ∨ p1) ∧ (p1 → p4)))) ∨ (True ∧ (p5 ∧ p5))) → (p3 ∧ (p3 ∧ (True → False))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319639120441544153672906912219 : (p4 ∨ (((p5 ∧ (p3 → (p1 ∨ p2))) ∨ (p5 ∨ p1)) ∨ (p1 ∨ (p4 ∨ ((((p2 → p3) → p4) → (True ∨ p2)) ∨ ((p4 ∨ p5) ∧ False)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47066747453520767058600516282 : (((((True → (p2 ∧ p5)) → (((p1 → p4) ∨ (p2 ∨ p2)) ∧ ((((p3 ∨ p1) → True) ∧ p1) ∨ p1))) ∨ (p2 ∨ False)) ∨ (p3 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161505386492929186110247302994 : ((p4 ∧ ((((p5 ∨ p4) ∧ p3) ∧ ((True ∨ True) ∨ p4)) ∧ ((p3 ∧ p3) ∧ ((False ∨ p1) ∨ p5)))) → (p2 → (p2 → ((p4 → False) ∨ p3)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h7.left
        let h16 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h15.left
        let h18 := h15.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- False on the left can always be used.
            apply False.elim h20
          case inr h21 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h18
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h7.left
        let h25 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h26 := h24.left
        let h27 := h24.right
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h28 =>
          -- Disjunctions on the left can always be decomposed.
          cases h28
          case inl h29 =>
            -- False on the left can always be used.
            apply False.elim h29
          case inr h30 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h27
        case inr h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h27
    case inr h32 =>
      -- Conjunctions on the left can always be decomposed.
      let h33 := h7.left
      let h34 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h35 := h33.left
      let h36 := h33.right
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h37 =>
        -- Disjunctions on the left can always be decomposed.
        cases h37
        case inl h38 =>
          -- False on the left can always be used.
          apply False.elim h38
        case inr h39 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h36
      case inr h40 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h36
  case inr h41 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h42 =>
      -- Disjunctions on the left can always be decomposed.
      cases h42
      case inl h43 =>
        -- Conjunctions on the left can always be decomposed.
        let h44 := h7.left
        let h45 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h46 := h44.left
        let h47 := h44.right
        -- Disjunctions on the left can always be decomposed.
        cases h45
        case inl h48 =>
          -- Disjunctions on the left can always be decomposed.
          cases h48
          case inl h49 =>
            -- False on the left can always be used.
            apply False.elim h49
          case inr h50 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h47
        case inr h51 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h47
      case inr h52 =>
        -- Conjunctions on the left can always be decomposed.
        let h53 := h7.left
        let h54 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h55 := h53.left
        let h56 := h53.right
        -- Disjunctions on the left can always be decomposed.
        cases h54
        case inl h57 =>
          -- Disjunctions on the left can always be decomposed.
          cases h57
          case inl h58 =>
            -- False on the left can always be used.
            apply False.elim h58
          case inr h59 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h56
        case inr h60 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h56
    case inr h61 =>
      -- Conjunctions on the left can always be decomposed.
      let h62 := h7.left
      let h63 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h64 := h62.left
      let h65 := h62.right
      -- Disjunctions on the left can always be decomposed.
      cases h63
      case inl h66 =>
        -- Disjunctions on the left can always be decomposed.
        cases h66
        case inl h67 =>
          -- False on the left can always be used.
          apply False.elim h67
        case inr h68 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h65
      case inr h69 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h65



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192084103553318904195855908268 : ((p4 → ((((p5 ∧ p1) → (p3 ∨ False)) → p1) ∧ True)) ∨ ((p3 → (p5 → (p4 ∨ p3))) ∨ ((False ∧ p3) ∨ (False → ((p3 ∨ p2) ∧ p2))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256490361228992340953300115753 : ((False ∨ p4) → ((p2 ∨ p1) ∨ ((p5 ∧ (p1 ∧ (((True → (p5 ∧ False)) ∧ ((p4 ∨ ((p4 ∨ p4) ∧ p3)) ∧ (p5 → p5))) ∧ p4))) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h17 := h11 h16
      -- We need to get the right conjuct of h17 based on <expert-advice>.
      let h18 := h17.right
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h22 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h23 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h24 := h11 h23
        -- We need to get the right conjuct of h24 based on <expert-advice>.
        let h25 := h24.right
        -- False on the left can always be used.
        apply False.elim h25
      case inr h26 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h27 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h28 := h11 h27
        -- We need to get the right conjuct of h28 based on <expert-advice>.
        let h29 := h28.right
        -- False on the left can always be used.
        apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800569744835330987892677233022 : (((p2 → (((((((p2 → p5) ∨ p4) ∧ ((p1 → p4) ∨ p1)) → ((p3 ∧ (p3 ∨ p2)) → p3)) ∧ p3) → (p2 ∧ (True ∨ p4))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59928270313144380505968963472 : (((p5 ∧ p5) → (p4 ∨ ((((p5 → ((p3 ∧ p3) ∨ True)) → ((p1 ∨ p2) ∧ (p2 ∨ False))) ∧ (True ∧ (p2 ∧ True))) ∧ (p5 → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680371329818802228133295926521 : ((((((((False ∨ p4) ∧ p3) ∨ p2) → (True ∧ (p3 ∨ (p2 → (p5 ∨ p5))))) → (p2 → (p1 → p2))) → (((p4 ∨ True) ∧ p5) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733433229990720416655904045465 : ((((p4 ∧ p1) ∧ ((p2 → ((p4 → ((p4 ∧ p3) ∧ (True ∨ (((p1 → p4) ∧ (p3 → p2)) ∨ (p4 ∧ p4))))) ∨ p5)) ∧ (p5 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741731538712714255989829132237 : ((((True → p2) ∨ ((((p1 ∨ (p2 → p5)) ∧ ((p2 ∧ p1) ∨ (((p4 → ((p3 ∨ p1) → True)) ∧ False) → False))) → (p1 ∨ p1)) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_204330655991529756290158074602 : (((p4 ∧ ((p5 ∨ p4) ∨ p4)) ∧ False) ∨ (((p5 → ((False → p5) ∨ (p5 ∧ (p5 ∧ p1)))) ∧ (p4 ∧ (((p2 ∧ False) → True) ∨ p5))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342990445603428445546271807077 : (p2 → (((p2 ∧ True) → (False ∨ p5)) ∨ ((p4 → (False ∨ ((p3 → (p4 → (((p1 ∨ p5) → p1) ∧ False))) ∨ ((False → p3) ∨ p1)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41260137853063655568352790041 : ((((((True ∨ p2) ∧ p5) ∨ ((p3 → (((p2 ∨ p1) ∧ ((p1 ∨ p3) ∨ False)) ∧ p4)) → p1)) ∨ (((False → p5) ∨ p3) ∨ p5)) ∨ p5) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117884178952679181262270326623 : ((p5 ∧ ((p1 → (((((((p5 → p2) ∨ ((True ∧ True) ∨ (p5 → p5))) → p3) ∨ p5) → (p1 ∨ p1)) ∧ p3) → p5)) → p3)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787519506139269532958595122647 : (((p4 ∨ (False ∨ ((p3 → (True ∧ (p4 ∨ p1))) ∨ (((p4 ∧ (p4 ∨ p5)) ∨ (p1 ∨ (p3 → p1))) ∨ (False ∨ (False → (p2 ∧ False))))))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320360257968981969912072706940 : (p4 ∨ ((p2 → p5) ∨ (((((p5 → p2) → (((False → (p2 → p3)) ∧ (((False → p2) ∧ p1) ∨ True)) → False)) → p3) ∧ (False ∧ p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_956025753495059397625282672438 : (((((p1 ∨ True) ∨ True) → (True ∧ ((((p5 ∨ (p2 → p5)) ∧ ((((False → (True → p1)) → p3) ∨ (p1 ∧ p5)) ∧ False)) ∧ p4) ∧ p1))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ True) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



