variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103919020930133028082641406375 : (((((True ∨ p1) → False) ∧ (((p1 → (True → p3)) ∨ ((((False ∨ p1) ∨ (p3 ∧ p4)) ∨ True) ∨ (p4 ∧ p5))) ∨ p5)) → p5) ∧ (p4 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      have h6 : (True ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
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
              -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
              have h14 : (True ∨ p1) := by
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h2, we can now drive its conclusion.
              let h15 := h2 h14
              -- False on the left can always be used.
              apply False.elim h15
          case inr h16 =>
            -- Conjunctions on the left can always be decomposed.
            let h17 := h16.left
            let h18 := h16.right
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h19 : (True ∨ p1) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h20 := h2 h19
            -- False on the left can always be used.
            apply False.elim h20
        case inr h21 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h22 : (True ∨ p1) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h23 := h2 h22
          -- False on the left can always be used.
          apply False.elim h23
      case inr h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- One of the premise coincides with the conclusion.
        exact h26
  case inr h27 =>
    -- One of the premise coincides with the conclusion.
    exact h27
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790204400101773562019839367916 : (((p5 ∨ (False ∧ (((False → ((p4 ∨ p4) ∨ ((p2 ∧ (((p1 ∨ p1) → ((p2 ∧ True) → p1)) → p3)) ∧ (False ∧ p1)))) ∧ p4) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115169050588850211087579584037 : ((((((p1 ∨ False) ∨ (p3 ∧ p1)) → (True → p3)) ∨ p3) ∧ (((((((False ∧ True) → True) ∧ p3) → p2) ∨ p3) ∨ p5) ∨ p1)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54072173274718469728885067341 : ((((True ∧ (p1 → True)) → ((p5 ∨ True) → (p2 → p2))) → ((((False → (p1 ∧ p1)) → p2) ∧ (p4 ∧ p2)) ∧ ((False ∧ False) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783352554614575363139305738434 : (((p3 ∨ (((((False ∧ p2) ∧ p5) ∨ p2) ∨ ((p5 → (p3 ∧ ((p3 → p4) ∨ True))) ∧ p2)) ∧ ((p2 → p3) ∧ ((p5 ∨ p1) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629897962123789411066004987976 : ((((((((p3 → p4) → (p1 ∧ p4)) ∧ (p3 ∨ p2)) → (((p1 ∨ (p4 ∧ ((False ∨ (p1 → p4)) ∧ p5))) ∨ p2) ∨ False)) ∨ p2) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119517558132109574858991440875 : ((p5 → (((((((p2 ∧ p3) ∧ p5) ∧ ((p3 → p1) ∨ False)) → p1) ∧ ((p3 ∨ p3) ∧ ((False ∧ p3) ∧ False))) ∨ p2) ∨ True)) ∨ (False ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50639799963590215469320263916 : ((((False → ((p2 → p4) ∧ ((True ∨ (p4 ∧ p3)) ∧ (p4 ∨ False)))) ∨ (((p3 → p5) → p2) ∧ p5)) → (((p3 ∧ p1) → False) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348750999992207666692318554158 : (p3 → (False ∨ (((p4 → (((False ∧ p1) → p4) ∧ p5)) ∨ (p3 ∧ p2)) ∨ ((((p1 → p5) → ((p5 → p4) ∨ p1)) ∧ True) ∨ (True ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617724727373868645370029217314 : ((((((p1 ∨ True) → ((p2 ∧ p3) ∨ p1)) ∨ (p3 → ((False ∨ p4) ∨ ((p1 ∨ p1) → (((p2 ∨ (p4 ∨ p5)) ∨ p1) → True))))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_115851532752246642094448528516 : (((p2 ∨ (p5 ∨ (p2 → p3))) ∧ (True → (p1 ∧ (((p3 ∨ p2) → (p4 ∨ (((p5 ∧ p4) → p2) ∨ (p3 ∨ True)))) ∧ p4)))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354769873012234051002336958650 : (p5 → (((p4 ∨ (p4 ∧ ((False ∧ ((p4 ∧ (p5 ∨ p2)) ∧ p4)) → p3))) → ((p2 ∧ (((p2 ∨ (p3 ∧ p3)) → False) → p3)) ∨ p3)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758235684909708065560153395504 : (((p1 ∧ (p5 → ((p2 ∧ (True ∧ p1)) ∨ (((p2 → p4) ∧ (p5 ∨ p1)) ∧ (((p2 ∧ ((p5 ∧ p1) ∨ p1)) ∨ False) ∧ (p2 ∨ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228232250125447286527166650377 : ((p5 ∧ (p5 ∨ True)) ∨ ((((False → (p5 → p2)) ∨ (p3 ∧ ((p5 → p1) ∨ (p1 → p4)))) → (True ∧ ((p5 → (p2 → p3)) ∧ False))) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False → (p5 → p2)) ∨ (p3 ∧ ((p5 → p1) ∨ (p1 → p4)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133625312673471022955592043049 : (((((p2 ∨ p1) ∧ (p2 ∧ ((p5 ∨ (((p5 ∧ False) → p1) ∧ True)) ∨ (((p4 ∧ p4) ∨ False) ∨ p5)))) → p3) ∧ p2) ∨ ((p2 ∧ p4) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112422473565107814826874693828 : ((((p2 → (((((p3 → p1) ∨ (p5 → p5)) → ((True ∧ p4) → p2)) ∧ p1) ∧ ((p5 ∨ p5) → (False ∧ False)))) ∧ True) → p5) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191886383431789762728132795705 : ((p4 ∨ (p2 → (((p3 ∧ p3) ∨ p1) ∧ (p3 ∨ True)))) ∨ (False → (((True → (((True ∨ p4) → p5) ∨ p2)) ∨ ((p4 → p3) → False)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164860984370286909953511126031 : (((p2 ∨ ((((p3 ∨ True) ∧ True) ∨ ((p4 ∧ p3) ∧ (p3 ∨ p4))) ∧ (False ∧ p4))) ∨ p1) ∨ ((p3 → (p3 ∨ (p4 ∨ (True ∨ p4)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341743551454288952277542064087 : (p2 → ((False ∧ ((p3 ∧ (((True ∨ ((p3 ∨ (False → p5)) ∨ p3)) ∧ (p3 ∧ (p3 ∧ p3))) ∧ ((p1 → p1) ∨ True))) ∧ p1)) ∨ (True ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42271902961675293179778200045 : (((p1 ∧ (((p4 ∨ p3) ∧ (p1 → p1)) ∧ (p2 → ((False ∧ p5) ∧ (((True → (p1 → False)) ∧ p2) ∨ (p2 ∧ (p2 ∨ True))))))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733760064795047631490699731587 : ((((p5 ∧ p2) ∧ ((True → (False ∨ False)) ∧ ((p4 ∧ (p5 ∧ (True ∨ p3))) → ((((p2 → True) ∨ (p2 ∨ True)) → p1) ∧ (True ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199830083815825423976213503327 : ((((p5 ∧ p2) ∨ (p4 ∧ p2)) ∧ (p2 → p4)) → (p4 ∨ (((p2 ∧ (((p3 ∧ ((p2 ∨ True) ∧ False)) → (True ∨ True)) ∧ p3)) ∧ True) → False))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652777986440931077571048248205 : ((((p2 ∨ (False ∨ (p3 → ((p1 ∨ p5) ∨ (p2 ∨ ((((p5 ∨ p4) → p3) → p5) → (p4 ∧ ((p1 → p4) ∧ p3)))))))) ∧ (p3 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49537286736868412108807744284 : (((((((p4 ∨ p5) ∧ (p2 → (p1 ∨ ((p2 → True) ∧ (False ∨ p3))))) ∧ (p1 ∧ p2)) → p3) → (p4 → p4)) → ((p3 → p4) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651745511455272651371105119290 : (((((True → p5) ∨ (True → (((p1 ∧ ((p1 ∨ ((p5 → ((p3 ∧ False) ∧ True)) ∨ p3)) ∧ False)) ∨ (p2 → p1)) ∧ p1))) ∧ (p5 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173360867426830293725301600802 : ((p3 → ((p3 ∧ (p2 → (p1 ∨ p1))) → (p2 ∧ (p3 ∧ ((p5 → True) → True))))) ∨ ((((False ∧ p5) → p4) → p4) → (p3 ∨ (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779995742129275043340179052156 : (((p2 ∨ (((((True → (True ∧ False)) ∨ (p1 ∨ True)) ∧ ((p3 ∧ ((((p4 ∨ p4) ∨ p5) ∨ p2) ∧ p5)) ∧ p1)) ∨ p2) ∨ (p2 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37560451766529586812379870919 : ((((p3 ∨ ((((True ∨ p2) ∧ p1) ∧ (p5 → (((((p4 → p2) → p1) ∧ (p1 → (p4 → p4))) → True) ∧ p2))) ∧ p3)) ∨ False) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119593839817349758427333052894 : ((p5 → (p1 ∧ ((p2 → ((((((p2 → p3) → p2) ∨ True) ∧ False) ∨ p5) → ((p1 ∧ p2) ∨ p5))) → (p4 ∧ (True → p1))))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148772822873061220054105094617 : (((((p5 ∧ p4) → (p1 → p1)) → p5) ∨ ((p3 ∧ (((p1 ∧ p1) → ((p1 → p1) → p1)) ∧ p3)) ∨ p5)) ∨ (p5 ∨ ((p5 → True) ∨ False))) := by
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
theorem thm_5_vars_51049783771159460324937649540 : (((p3 ∨ (((p1 → ((p2 → p4) ∧ p3)) ∨ (False → (p4 → p1))) ∧ ((False ∨ False) ∨ True))) ∧ (((False ∨ p1) ∨ False) ∨ (p2 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190863246078339423793083149165 : ((((p5 ∧ ((p2 ∨ p2) ∧ p3)) → True) → (p4 → p5)) ∨ (((False → (p4 ∧ (p2 ∨ ((p2 ∧ ((True ∨ True) ∨ p4)) → p1)))) ∨ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328782292969717055329451227618 : (True → (((p1 ∨ (((False ∧ p4) → False) ∧ (p2 ∧ p3))) ∧ p5) ∨ (((((p3 ∨ ((p2 ∧ True) → p3)) ∨ p3) → (p3 ∧ p2)) ∨ True) ∨ p1))) := by
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
theorem thm_5_vars_200734750097678347221869087024 : ((p3 ∧ (((p2 ∧ p4) → False) ∨ (p4 ∨ p1))) → ((((p2 ∨ (((p5 → False) → (p1 ∧ False)) ∧ False)) → p5) ∨ (p4 ∨ False)) ∨ (p3 ∨ p1))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672976319563061075019032213604 : (((((p4 ∨ ((True → ((p1 → p1) ∧ (p4 ∧ p4))) → ((p4 ∧ p4) ∨ p3))) ∧ (p2 ∧ (p3 → (p4 ∨ p3)))) → ((True ∧ p5) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44288798707207018910402330566 : ((((((p5 → ((p4 → False) ∧ (p4 → (True ∧ (p5 ∨ p4))))) ∨ p3) → (p4 ∨ p4)) ∧ (((p5 → (p2 ∨ p5)) ∧ p3) → p3)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118809348943694927382816103730 : ((True → (((p1 ∧ ((p2 ∧ (p3 → (p3 ∧ p1))) ∧ ((((p4 ∧ (True ∧ p5)) → (p2 → True)) → p4) ∨ p4))) ∨ True) ∨ True)) ∨ (p5 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612472020945992714080482006315 : ((((((((p5 ∨ p3) ∧ p2) ∨ ((False ∧ (((p4 ∨ (p4 ∨ p5)) → p3) ∨ ((p3 ∨ p2) ∧ p3))) ∨ p4)) ∧ True) ∨ (True ∨ False)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62807565339854414511049725142 : ((p4 ∧ ((((p4 → p4) ∧ (p5 ∧ p4)) ∨ ((True ∨ (p4 → p3)) ∨ (p4 ∨ True))) → ((p1 ∧ (p3 ∨ p5)) → (p3 → (p2 ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609492092932373850739322394521 : (((((p1 ∧ ((((((False → p4) ∨ ((p5 ∨ True) → (((p5 → p5) ∧ p4) → True))) ∨ p5) ∧ False) ∨ p2) ∨ (p2 ∨ p2))) ∨ p1) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_354924912876004418421586157878 : (p5 → ((p2 ∨ ((p3 ∨ True) → ((((((p2 → (p4 ∨ p1)) ∧ p4) ∧ (p5 ∨ (p5 ∧ (True → (p4 → p1))))) ∧ p4) ∨ p3) ∨ p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62673084362980954350313324674 : ((p4 ∧ (((p3 → True) → ((p1 → (((p1 ∨ p1) ∧ (p3 → p1)) ∨ (p2 ∧ (True ∧ (p3 ∧ (p2 ∨ p2)))))) → (p2 ∨ False))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21429030105786644508458811954 : (((((p2 ∨ ((p2 ∧ p5) ∨ (p5 ∧ p5))) ∧ p1) → p5) ∨ ((((False ∧ p3) ∨ p5) ∧ (p1 → ((p5 ∨ p5) ∧ p1))) ∨ (False → p1))) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150529342103011374268565737131 : ((((((False → p1) ∧ (False ∨ p3)) ∨ ((p2 ∧ p2) ∨ False)) → ((p5 ∧ (p4 ∧ False)) ∧ (True → p4))) ∧ p3) → (p4 ∧ (p2 ∧ (p1 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((False → p1) ∧ (False ∨ p3)) ∨ ((p2 ∧ p2) ∨ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h12 : (((False → p1) ∧ (False ∨ p3)) ∨ ((p2 ∧ p2) ∨ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h13
    -- False on the left can always be used.
    apply False.elim h13
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h14 := h10 h12
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- False on the left can always be used.
  apply False.elim h17
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
  have h20 : (((False → p1) ∧ (False ∨ p3)) ∨ ((p2 ∧ p2) ∨ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h21
    -- False on the left can always be used.
    apply False.elim h21
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h19
  -- We have shown the premise of h18, we can now drive its conclusion.
  let h22 := h18 h20
  -- We need to get the left conjuct of h22 based on <expert-advice>.
  let h23 := h22.left
  -- We need to get the right conjuct of h23 based on <expert-advice>.
  let h24 := h23.right
  -- We need to get the right conjuct of h24 based on <expert-advice>.
  let h25 := h24.right
  -- False on the left can always be used.
  apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165036181864293026618930010167 : ((((p1 ∧ p3) ∧ (p5 → (((p3 ∧ True) → p1) → (((p1 → True) ∨ True) ∨ False)))) → p5) ∨ (True ∨ (((p5 ∧ True) ∨ (p2 ∧ p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60753412100652743621662217180 : ((True ∧ ((p2 → (False ∨ False)) → (True ∧ (p4 ∨ ((p5 ∨ ((((False → False) ∨ p4) → (p1 → p2)) ∨ (p2 → (p1 ∨ True)))) → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114906552961892001105885308638 : (((((((p4 → False) → True) → (p5 ∨ p4)) ∨ ((False ∧ p3) → True)) ∧ p4) → ((p4 → (True ∨ ((False → True) ∧ True))) → False)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64789068022662928450113919188 : ((p2 ∨ ((((p2 ∧ ((p4 → (p5 ∧ p3)) ∧ (p5 ∧ (p4 ∨ p4)))) ∨ False) ∨ (((((p1 → p2) ∧ p1) ∧ p3) → True) ∨ p1)) ∨ p4)) ∨ p2) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147151368628085912751042354275 : (((p2 ∧ (p5 ∧ (((p1 → ((p5 → ((True ∨ False) → True)) ∨ True)) → p1) → (p5 → (p4 ∨ p2))))) ∧ p1) ∨ (p5 ∨ (False → (p2 → p1)))) := by
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
theorem thm_5_vars_258788361173969592190608783042 : ((True → False) → ((((p2 → ((p3 → p4) ∧ False)) ∧ p5) → p2) ∧ ((p4 ∨ False) → (p3 ∨ (p5 ∧ (True → ((p5 → (p2 ∧ p1)) → p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46637521389901357800249308405 : (((p5 ∧ ((p1 → (False → (p5 ∨ (p4 ∨ (((True ∧ ((p1 ∧ False) ∧ ((p4 → p1) → False))) ∨ p2) → True))))) → p5)) ∧ (p2 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197921839877373840396266475684 : (((p5 ∨ (p4 → p3)) → ((p5 ∨ False) ∨ p4)) ∨ (p2 → (p2 → (((True ∨ (p2 ∨ p4)) ∨ p4) ∨ (p2 ∧ ((p4 ∧ (True → p2)) ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115747222044351956632295805468 : ((((p1 ∨ p4) → (p5 ∧ (p1 → p5))) → ((((p3 ∨ p4) → (True → (p3 ∧ (False ∧ ((p1 → True) → p2))))) → p4) → p2)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135388839376361279633786421265 : (((((p2 → True) ∧ (((((False ∨ (False ∨ p5)) → p1) ∨ p2) ∨ p5) ∨ p4)) ∧ (p5 ∧ True)) ∨ (p4 → (p3 ∨ p2))) ∨ (p3 ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245224661806178359197697995876 : ((p2 ∧ p1) ∨ ((True → (p1 ∧ ((p4 → (True → (p1 ∧ (p1 → (((p3 ∧ p3) ∨ (p5 ∨ p5)) ∧ False))))) ∧ ((p3 → False) ∨ p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_95179180032351280570596160669 : ((p4 ∧ ((False → (p1 ∧ (((p1 ∨ True) → ((p2 ∨ p1) → False)) → True))) → ((((p4 ∧ p1) → p3) ∧ ((p5 ∨ False) → p1)) ∧ False))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (False → (p1 ∧ (((p1 ∨ True) → ((p2 ∨ p1) → False)) → True))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116401841478896050395982440875 : (((p4 ∧ (p3 → False)) → ((p2 → p3) ∧ (((p4 ∨ ((p2 ∨ False) → (((False ∨ False) ∧ p1) ∨ p1))) → p2) ∨ (False → p4)))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670453910135394713923239321698 : (((((p2 ∧ p5) ∧ ((p3 ∧ True) ∧ ((((((p4 ∨ True) ∧ (p2 ∨ (p1 ∨ True))) → True) ∨ p1) ∧ p2) ∨ p5))) ∨ (False → (True → True))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629652821811651652038959273108 : ((((((p2 → (p5 ∧ ((p5 → (p4 → ((p4 ∧ True) ∨ (((p3 → p1) → p5) → p5)))) → p2))) → (True → (True → p1))) ∨ p2) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723951729190729523841216659891 : ((((False ∧ (p1 ∧ p4)) ∧ (False ∨ (((False ∨ (p3 → p3)) ∧ p3) → (((p5 ∨ (False ∧ p4)) ∨ p4) → ((p1 ∧ (p5 → p5)) ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115037452015080385568338505560 : (((((p2 ∧ p3) ∨ (p5 ∨ ((True ∧ (False ∧ p3)) → p4))) ∧ p3) ∨ ((p3 ∨ (False ∧ (p5 → p4))) ∨ ((p2 ∧ False) ∨ p2))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184107186155574655325624944233 : ((((p1 ∧ p3) ∨ (p3 ∧ ((False ∨ (p5 → p2)) ∧ p1))) ∨ True) ∨ (((p2 → (False ∧ p3)) ∨ p4) → ((p1 → (p5 ∧ p5)) ∧ (p5 ∧ p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690375820492349847842681551752 : ((((p4 → (p5 → ((((((p2 ∨ (p3 ∨ p3)) ∧ False) ∧ p2) ∧ p3) ∧ False) ∧ p3))) ∨ ((False → (True → ((p5 → p3) ∧ p3))) ∨ p5)) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174713474322686117604064994626 : (((False → (False ∧ p1)) ∨ (p5 ∨ (False ∨ (((p3 ∨ p5) ∨ (True → p1)) ∧ False)))) → ((((p5 ∧ p2) → (True ∨ True)) ∧ p3) → (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- False on the left can always be used.
            apply False.elim h13
          case inr h16 =>
            -- False on the left can always be used.
            apply False.elim h13
        case inr h17 =>
          -- False on the left can always be used.
          apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305017835366001562631444215634 : (p1 ∨ (((p3 ∨ p2) ∧ (((p4 → p5) → ((p2 ∧ (False ∧ p5)) → (True ∨ (p1 → p2)))) → (p5 → (p5 ∨ p2)))) ∨ (True → (False → False)))) := by
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
theorem thm_5_vars_308373081907382658670471057048 : (p2 ∨ ((((p3 ∧ ((p3 ∨ (p3 → (((p1 ∧ ((p3 → p4) ∨ p5)) ∧ p5) ∨ (p3 ∨ ((True → p5) → p1))))) ∧ p5)) ∨ p4) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227440781148604183162260527383 : (((p5 → p4) → False) ∨ (p3 → ((((p2 ∧ p1) ∧ ((p2 ∧ (((p1 ∨ True) ∧ p5) ∨ p5)) ∨ p1)) ∨ (p5 ∨ (False ∨ (p3 ∧ True)))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263484238456022738008289313118 : (True ∧ ((p2 ∧ (p1 ∧ ((p1 ∨ ((True ∨ (False → False)) ∧ (p2 ∧ ((True ∧ p2) → p4)))) ∨ (True ∨ (True ∧ p5))))) → ((False ∨ p1) ∧ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h10.left
        let h13 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h10.left
        let h16 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  -- Conjunctions on the left can always be decomposed.
  let h22 := h1.left
  let h23 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h23.left
  let h25 := h23.right
  -- Disjunctions on the left can always be decomposed.
  cases h25
  case inl h26 =>
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h27 =>
      -- One of the premise coincides with the conclusion.
      exact h27
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h30.left
        let h33 := h30.right
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h30.left
        let h36 := h30.right
        -- One of the premise coincides with the conclusion.
        exact h24
  case inr h37 =>
    -- Disjunctions on the left can always be decomposed.
    cases h37
    case inl h38 =>
      -- One of the premise coincides with the conclusion.
      exact h24
    case inr h39 =>
      -- Conjunctions on the left can always be decomposed.
      let h40 := h39.left
      let h41 := h39.right
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614780421591432041573957820071 : ((((((p4 → ((p4 → p3) ∨ p1)) → (((p2 ∨ (p5 ∧ p3)) ∨ (p5 → False)) ∨ (False → p1))) ∨ (((False ∨ True) → p3) → True)) ∨ False) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114301031468060586777692842078 : (((((((False ∨ (p3 → p4)) → p4) → ((p4 ∧ p5) ∧ p3)) → p1) → (p3 ∧ (p3 ∧ p4))) ∧ (p1 ∧ (p4 → (p2 → p5)))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64777865748357439969211218536 : ((p2 ∨ (((((True ∧ (p1 ∧ (((False → p4) ∧ ((p1 ∨ (p2 → ((False ∧ p1) ∧ p4))) ∧ True)) ∧ p4))) → False) ∧ p5) → p2) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305350471472484418762865673191 : (p1 ∨ ((p2 ∧ (p1 ∨ (p5 → ((p3 → (True ∧ ((False → (p5 ∧ p4)) → p4))) ∧ (False ∧ p4))))) → (((p4 → False) ∧ (p5 → p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49197419465460842739037583637 : (((((False ∧ False) ∨ False) ∨ (((p3 → ((False → p3) → (p1 ∨ p5))) ∧ (p5 ∧ p4)) ∧ ((p4 ∨ False) ∨ p1))) ∨ (p4 → (True ∨ p4))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65286326615987315560800568374 : ((p3 ∨ (((((p1 ∧ ((p1 ∧ ((p5 → False) ∨ p2)) ∨ (((p1 → p5) → p5) ∧ (False ∨ p3)))) ∧ p3) ∧ True) ∨ p1) ∨ (p5 → p5))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314314346629373599992562749628 : (p3 ∨ ((((True ∧ (p3 → ((((p2 ∨ True) → p3) → p1) → p2))) ∧ (True ∧ p2)) ∧ (p4 ∨ ((p5 → False) ∧ p3))) → ((p3 ∧ p1) ∨ True))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h10 =>
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
theorem thm_5_vars_780447947895769085960321049742 : (((p2 ∨ (((((p3 ∧ p4) → p5) ∨ (p5 → (p3 ∧ False))) ∧ (p4 → (p1 ∧ True))) ∧ ((True → ((p4 ∨ p2) ∧ (True ∨ False))) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105936691243864454876646750186 : ((((p2 ∧ ((p1 → (p5 ∨ (True → p1))) ∧ p2)) ∧ ((p2 ∨ p3) ∨ p5)) ∨ (((p1 ∧ True) ∨ ((p4 ∧ p2) → True)) ∨ p2)) ∧ (False → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337146513686730005863499298112 : (p1 → ((p2 → (((p5 → True) ∧ p1) ∧ ((False ∧ ((p4 ∨ (p3 ∧ p1)) → ((p1 ∨ p4) ∨ (p4 ∧ (True ∨ p4))))) ∨ p4))) ∨ (True ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342273546436500708683787016688 : (p2 → ((((p2 ∨ ((p2 → (p2 → (p4 ∨ ((False → (True → p5)) ∧ True)))) ∧ p3)) → False) ∨ p2) ∨ (p4 → (((p2 ∨ p5) ∧ p2) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115005996614205874098111682310 : ((((p3 ∧ (p1 ∨ p5)) ∨ ((((False ∧ p2) ∧ p1) → p5) ∨ False)) ∧ ((((p1 → p3) → p4) → ((p3 ∨ True) ∨ p2)) ∧ p4)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40999150022890728941564645838 : ((((p2 → ((p4 ∨ p1) → ((((True ∨ p4) → False) ∨ (p2 ∨ p4)) → (False ∨ ((p3 → (False → p3)) ∨ True))))) ∨ (p2 ∨ True)) ∨ p1) ∨ p1) := by
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
theorem thm_5_vars_197859422152325731232354180250 : (((p5 → (p3 → False)) ∨ ((p2 ∨ p3) ∧ p2)) ∨ (p2 → ((((((True ∧ p3) ∨ True) ∨ p3) ∨ False) ∨ (p1 ∨ (True ∧ (p1 → False)))) ∧ p2))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608138432750147017283092995467 : (((((((False ∨ (((p2 ∨ p4) ∨ p4) ∨ (True ∨ p4))) → (((p4 ∧ ((True ∧ False) → False)) ∧ (p3 → p5)) ∨ p3)) ∧ p4) ∨ p5) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_739093554539522708536669081605 : ((((p3 ∧ p5) ∨ ((((False → (True ∧ p3)) ∧ (((True → ((False → True) → (p1 ∨ (p4 ∨ p4)))) ∧ True) ∨ (False ∧ p2))) ∨ True) ∨ p3)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147338405943298560525249062698 : ((((p5 ∨ ((p3 ∨ (p1 → (((p2 ∧ p5) ∧ (p1 ∧ p1)) → (True ∨ False)))) → p5)) ∨ (p5 ∨ p4)) ∨ p5) ∨ ((True ∧ True) ∨ (p2 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785525012531872022380776518300 : (((p4 ∨ ((p4 ∧ ((p3 ∧ (((p1 ∧ p3) ∨ (p1 → (True ∧ ((False → False) ∨ p1)))) ∧ (p1 ∨ (p4 ∧ (p5 → p3))))) ∧ True)) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_218470350398657808064434990607 : (((True ∨ False) → (p1 ∨ False)) → (p2 ∨ ((p2 → ((p3 ∨ (((p2 ∧ (((True ∧ p3) → p5) ∨ False)) ∧ True) ∨ False)) → p1)) ∨ (True → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h10.left
        let h13 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h15 =>
          -- False on the left can always be used.
          apply False.elim h15
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8972254023870455277734529559 : (((((p3 ∧ (((p3 ∧ (p5 ∨ (p4 ∨ ((p1 ∨ True) ∨ p1)))) ∨ p2) → False)) ∨ False) ∨ (p3 → (p1 → ((p3 ∧ p1) ∨ True)))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_394478377204080400593434018485 : (((((False → True) → (True ∧ (True → ((False → (p4 ∧ (p2 ∨ p5))) → (((((p4 ∨ p4) ∧ p5) ∧ (p2 → p1)) → p3) ∨ False))))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_324564722114854069215567496541 : (p5 ∨ ((p4 → ((p2 ∧ p4) ∨ p4)) → (p1 → (True ∧ (((p1 → (p4 ∨ (((p5 → False) → p3) ∨ (p2 ∧ p2)))) ∧ (p1 → True)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150004161639665638451541191013 : ((p5 ∨ (((((p2 ∨ (((p5 ∨ p3) → p4) ∧ ((p3 ∨ (p2 ∧ False)) ∨ True))) ∧ True) ∨ p3) → p5) ∨ True)) ∨ ((p2 ∨ (False → p1)) → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234029641407106529638822587867 : ((p5 ∨ (False → True)) → ((p3 ∨ (True → ((p1 ∧ p2) ∧ (((((p4 ∧ (p4 → True)) → p2) ∧ (p3 ∧ p5)) ∧ True) ∧ (p5 ∨ False))))) ∨ True)) := by
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
theorem thm_5_vars_329202498594458836284966505071 : (True → (((p3 ∧ True) ∨ True) ∧ ((p2 ∨ ((p1 → (p5 ∨ p3)) → (p1 ∨ ((p1 ∧ ((p2 ∧ p5) ∨ True)) ∨ False)))) ∨ ((p3 ∨ p5) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44811345256771225769150764033 : ((((p4 ∧ (True ∧ p3)) ∧ ((((((True ∧ p4) → (p4 ∨ (p1 ∨ True))) ∨ p5) ∨ True) → (((p4 ∧ False) → p3) → False)) → False)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197406254690354925142784568390 : (((False → (p4 ∧ ((p3 → p3) ∨ p3))) → p2) ∨ (((p5 → (False → p3)) → (((False → p3) ∨ (p2 ∨ p3)) → (p5 → (p2 ∨ p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659134305485495373621071936742 : ((((p3 → ((((p4 → (((p1 → (p1 ∧ False)) → p3) → (p2 ∧ p2))) → p5) ∧ (p2 ∨ ((True ∨ p1) ∧ p4))) → p1)) ∨ (p5 → p5)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_350940831605193181706026799595 : (p4 → (((((p4 ∧ p3) ∧ (p4 ∧ False)) ∧ (((p2 → (p5 ∧ p3)) ∧ (False ∨ (p5 ∧ p1))) → (p3 → p1))) ∨ (p5 → False)) ∨ (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185501146775791699347210293657 : ((p2 ∨ ((p2 ∨ (p3 ∧ False)) ∧ (((p5 → p3) → p2) → p4))) ∨ (p2 → ((((((p2 → (p5 ∨ p3)) → p2) ∧ p4) ∧ p1) → p1) ∨ p1))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264165297088627139199385019248 : (True ∧ ((((p1 ∨ p4) ∧ p2) ∨ (False ∨ (p2 ∨ True))) ∨ ((((p1 → p5) → p1) ∨ (p5 → False)) ∧ ((((False ∨ False) ∨ p3) ∨ p3) ∧ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_252645873688521304423201655231 : ((p5 → p4) ∨ (((True → (True ∧ (True ∧ (p5 ∧ p1)))) → (((p5 ∨ False) → (p2 ∨ (p5 ∨ False))) ∧ (p4 ∨ p2))) ∨ (True ∨ (p2 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



