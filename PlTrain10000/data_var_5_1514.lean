variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158186111627696147251535652486 : (((p2 ∨ ((p3 ∧ False) → p5)) → ((p5 ∧ (((p2 ∧ p4) → (p4 ∧ p2)) ∧ (True ∧ True))) ∨ p2)) ∨ ((True ∨ ((p1 ∧ p3) ∨ p3)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340793160232296179259006357863 : (p2 → ((((p5 ∨ p3) ∧ ((((p5 ∧ ((((False ∨ False) ∨ True) ∨ p3) → (p1 ∧ p2))) ∨ (p1 → p1)) → (p4 ∧ p4)) ∧ p4)) → p3) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693658673805318343579046607234 : ((((((((p2 → p2) → True) → (p1 ∧ (p3 ∧ p1))) ∨ (p1 ∨ p5)) ∨ p2) ∨ ((False ∧ True) ∨ (p3 → (p2 → (p3 → (True ∨ False)))))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107367865381655343637516556373 : (((p5 ∨ (p4 ∨ p4)) ∨ (((p5 → p5) ∧ (((((False ∧ p5) → ((p3 ∧ p5) ∨ p4)) ∧ p5) ∧ p3) ∨ False)) ∨ (p2 ∨ True))) ∧ (True → True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156849397481038362706962237542 : (((p4 → (p3 → (p4 → (((p2 ∨ False) ∧ p5) ∧ ((p2 ∨ (p5 ∨ p1)) ∨ (False → True)))))) ∧ False) ∨ ((p1 → (p1 → (True → p1))) ∨ p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698538840464446381076145192353 : ((((((True → (p3 → True)) ∧ p3) ∨ ((p1 ∧ p5) ∨ (p1 → p3))) ∨ ((p5 → ((p5 ∨ (p3 ∨ (False → p3))) ∧ False)) ∨ (True ∨ p1))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630677545933551437612777184832 : (((((p1 → (((True ∨ (p5 → ((((True ∧ p1) ∨ (True → p3)) → (p4 ∨ p5)) ∨ (p3 ∨ True)))) ∧ (p1 ∨ p1)) ∨ False)) ∨ False) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259173801925797378004684975284 : ((False → True) → (p3 ∨ (((p5 ∧ False) ∧ (((True → (p4 ∨ p2)) ∧ (p3 ∨ ((False ∧ True) ∧ ((p3 ∧ (True → p1)) → p4)))) → p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116448493214795864151295396475 : (((p5 → (p2 → p4)) → (((p5 → False) → (((p4 → (p1 ∧ ((p4 → p4) ∨ p4))) ∧ False) ∨ p2)) ∨ (p4 → (p4 ∨ p3)))) ∨ (p2 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249835650176153397089239032093 : ((True → False) ∨ ((((p3 → (p1 ∧ (((p4 ∨ False) ∧ ((p1 ∨ (p4 ∧ p5)) ∨ (False → (p2 ∧ p5)))) ∨ p2))) ∧ (p2 ∧ p4)) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208194850768799681735855936316 : (((p4 ∨ (p2 ∧ p3)) → (p5 → False)) → ((True ∧ ((p1 → (True ∧ ((p1 ∧ p2) ∨ ((p1 ∨ p4) → (p3 → False))))) ∧ p1)) ∨ (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_823655409904026709974045899937 : (((((p1 → (p3 ∧ ((p1 ∨ False) ∨ p3))) → (((p1 ∧ (((((p3 ∨ p5) → p4) → p5) ∨ (p3 ∧ p3)) → p4)) ∨ True) → False)) ∧ p3) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p1 → (p3 ∧ ((p1 ∨ False) ∨ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : ((p1 ∧ (((((p3 ∨ p5) → p4) → p5) ∨ (p3 ∧ p3)) → p4)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60679507958920297032406940275 : ((True ∧ ((p1 ∧ (((p4 ∧ p5) → (p1 ∨ ((p5 → p2) ∨ (False → p5)))) → p5)) ∨ (False → ((p4 ∨ (False ∨ (p1 ∨ p4))) ∧ p1)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_166481861227608502481314708537 : ((p3 ∨ (((p3 → p3) → (p4 ∨ ((p2 → True) ∧ (True ∧ (False ∧ p3))))) ∨ (p3 → p1))) ∨ (((True ∨ p3) ∨ p1) ∧ (p4 → (p4 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58310154477413049740724882274 : (((True ∨ p5) ∧ ((((True ∧ ((p2 → False) ∨ (p3 → (((p2 ∧ (p4 ∨ False)) ∧ (p1 → True)) ∧ p4)))) ∨ False) ∨ (p4 ∧ p2)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50531290268585041346649227248 : (((((((p5 ∨ p1) ∧ (p3 ∨ ((p4 → p3) ∧ p3))) ∨ ((p2 → (p2 ∧ p1)) ∨ p1)) ∨ p4) ∨ True) → (p4 → (False ∨ (False ∨ True)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h9 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h10 =>
            -- Conjunctions on the left can always be decomposed.
            let h11 := h10.left
            let h12 := h10.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h15 =>
            -- Conjunctions on the left can always be decomposed.
            let h16 := h15.left
            let h17 := h15.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43240114083709940178254197977 : ((((p4 ∨ ((((p2 ∨ p1) ∨ False) → (p2 ∨ ((((p2 → (((p1 ∧ p5) ∧ p5) ∨ True)) → True) ∧ False) → p5))) ∧ p5)) ∧ p1) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147728788798497718297416591528 : (((((p5 ∨ p1) ∨ (False → (p3 ∧ p3))) ∨ ((((p5 ∨ (p5 ∨ True)) ∨ p2) ∧ p2) ∧ (True ∨ p2))) → False) ∨ (((True ∨ p4) ∨ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198900586945149150928627030696 : ((p3 → ((p2 → (True ∨ (False ∧ p1))) → p4)) ∨ ((((p4 ∧ (False ∨ (p2 ∨ True))) ∨ True) → p1) → ((True → (p1 ∨ (p1 ∧ p3))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p4 ∧ (False ∨ (p2 ∨ True))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191561746641133246071482628538 : ((p1 ∧ (p2 → (((p4 → (True ∨ True)) ∨ p4) → False))) ∨ (True ∨ (((True → (True → ((True → ((p4 ∧ True) ∨ True)) → p2))) ∧ p3) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148590457966953295817188596817 : (((((True ∧ p5) ∧ True) ∧ (p1 → ((False ∧ p5) ∨ True))) ∨ ((p4 ∧ (p1 ∧ (False → p4))) ∧ (False ∨ p4))) ∨ ((True → (True ∨ p3)) ∨ p3)) := by
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
theorem thm_5_vars_765639417431412280553661325020 : (((p4 ∧ (((p2 ∨ (p4 ∨ p1)) → (((p4 → (True → p3)) ∨ p1) ∨ True)) ∧ ((p1 ∨ (p4 ∨ (p5 ∧ p2))) → (p2 → (p2 → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328982145387129170275535965959 : (True → (((p5 ∧ (False ∨ (False ∨ p1))) ∨ p4) ∨ ((((p1 ∨ p3) ∧ p1) → ((False → p2) → (True ∨ p4))) ∨ (True ∧ ((p5 ∨ p5) ∧ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319064248084615177675492258456 : (p4 ∨ ((p4 ∨ (((p2 → p1) ∨ True) ∧ ((((p3 → ((True ∨ True) → p4)) ∨ p1) ∧ False) ∨ (p3 ∨ True)))) ∨ (p4 ∧ ((p4 ∧ p4) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_57169704952783278668938487828 : ((((p3 ∧ p5) ∨ p3) ∨ ((((p3 → (True → False)) ∧ (((((p2 ∧ ((p5 ∧ p4) → True)) ∨ p2) → p4) ∧ p3) ∧ True)) → p5) ∨ p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h8
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115022979923751671914801613846 : (((p1 ∨ ((p5 → False) ∨ (False ∨ (p3 → (p3 ∨ (p4 ∧ False)))))) ∧ ((p4 ∨ (p2 ∧ ((p1 → p3) ∧ p3))) ∨ (p3 ∨ True))) ∨ (p3 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217880026130451294803201390110 : (((p1 → (p5 ∨ p2)) → p3) → (((p2 ∧ (True → ((True → True) ∧ (p5 ∨ p1)))) → p3) → ((((p3 ∨ p1) ∨ True) → p5) → (p3 ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (p1 → (p5 ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : ((p3 ∨ p1) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h4
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165064411241502788617590071817 : (((p1 ∧ (p1 ∨ (p3 → ((((False ∨ p5) ∨ (p2 → p2)) ∨ p5) ∨ (p4 → False))))) → p4) ∨ (((((True ∧ p4) → p4) ∨ False) → p5) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True ∧ p4) → p4) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232220769772047362289244922228 : (((p1 → False) → p1) → ((((p2 ∨ ((p4 ∧ p3) ∧ p3)) → p5) ∨ ((p5 → p2) ∨ ((False ∨ (True ∨ p3)) ∧ True))) ∨ (p2 ∧ (False → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_724105491246476947914252179142 : ((((p2 ∧ (p1 ∧ p3)) ∧ (p5 ∧ (p1 → (False ∨ ((p1 → ((True ∨ p5) ∧ (((p5 → (p3 ∨ p4)) → (False → True)) ∧ p1))) ∨ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167695558443448452820453386577 : ((((((False → p5) ∧ (p3 ∨ p3)) ∨ p1) → ((p5 → p2) ∧ p4)) ∧ (p3 ∨ (True ∧ p1))) → ((p5 ∨ (True ∨ False)) ∨ (p4 ∧ (p2 ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665496211362810862570869163257 : ((((((p2 → (((p1 ∧ (((((p1 ∧ (p4 → p1)) → p2) ∧ True) ∨ p2) ∨ p1)) ∧ p1) → False)) ∨ False) ∨ p2) ∧ ((True ∧ p2) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213411118659738193126994032112 : (((p2 ∨ (p2 ∧ p2)) ∧ False) ∨ (p1 → (((((((((p3 → p4) → False) ∧ p5) → False) ∨ p1) ∨ p4) → False) → ((p3 ∧ p2) ∧ p1)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((((p3 → p4) → False) ∧ p5) → False) ∨ p1) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : ((((((p3 → p4) → False) ∧ p5) → False) ∨ p1) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49684689205185233625554343460 : ((((p3 → p5) ∧ ((((False → (p1 ∨ p1)) ∧ (p2 ∨ (False → (p5 → p3)))) ∨ (p5 ∨ p1)) → (True ∧ p4))) → (p2 ∧ (p3 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49012135432694097165276310671 : ((((((p2 ∨ ((((p5 → (True → (False ∧ (p3 ∧ p5)))) → p2) ∧ p2) ∧ (p4 ∨ p4))) ∨ p3) → p3) → p4) ∨ ((True → False) → p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_336465399378181860326134794712 : (p1 → ((p1 → ((p1 ∨ (True ∨ (p4 ∨ ((p4 ∧ True) → True)))) ∧ (True → ((((p4 ∧ (False ∨ (p1 ∨ p3))) ∨ False) ∧ False) ∧ False)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255988187887143102235266895135 : ((True ∨ p3) → ((((((p5 ∨ (p3 ∧ (p4 ∨ (p3 ∨ p2)))) → p3) ∨ p3) → False) ∨ (p2 → (p3 ∨ p5))) ∨ (((p2 ∨ True) ∨ p5) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
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
theorem thm_5_vars_641732854338289712916829419956 : (((((p3 ∨ True) → (((((((p5 ∧ ((False → False) ∧ p4)) → True) → p4) ∧ p2) → ((False ∨ p3) ∨ (True ∧ True))) → p1) ∨ p4)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42340298073550387626133745838 : (((p3 ∧ ((p3 → ((p5 ∨ ((((p1 → p4) ∨ ((False → p5) ∨ (True ∧ p2))) ∧ p1) ∨ (True ∧ p2))) ∧ p1)) ∧ (p3 → p2))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662289854652206588195814172824 : ((((((p3 → (True → False)) → (True → ((p1 ∧ p1) ∧ False))) → (p1 ∧ (((p1 ∧ (p2 ∨ p1)) ∨ (p4 → p5)) → p2))) → (p3 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159219147530927717234756130831 : ((p2 → (p5 ∧ ((True ∨ p1) → (p5 ∨ (((p3 ∨ False) ∨ False) ∧ ((False ∧ (p2 → True)) → True)))))) ∨ ((False ∧ (True → (p5 → True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165734924807816484425973091328 : ((((p2 → (True ∧ False)) ∧ False) ∨ (((p2 ∧ (p5 ∧ (True ∧ p2))) → (p3 ∨ False)) ∧ p3)) ∨ ((p2 → ((False ∧ (p3 ∧ p1)) → p1)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57116277697219425816988464531 : ((((p3 ∨ p1) ∧ p4) ∨ ((p5 ∧ ((p4 ∨ p2) ∨ (True → (False ∧ True)))) ∨ (p2 → (((p3 → p5) ∧ ((p4 ∧ False) ∨ p4)) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56708777352926389347365835266 : ((((p4 ∧ p2) ∨ p1) ∧ ((p4 ∨ (((p2 ∨ p2) ∧ True) → (False ∨ (((p3 → (p1 → p3)) → (p3 → True)) → p2)))) → (p4 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159107730759426105424790610802 : ((True → (False ∨ ((False ∧ ((p5 → True) ∨ (((p3 ∧ (False → p4)) ∧ (p5 ∨ p3)) → p2))) ∧ p2))) ∨ ((p5 → (p5 ∧ True)) ∨ (False ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214650674481150722599265666255 : (((p2 → p3) ∧ (p1 ∨ False)) ∨ ((((True ∧ p4) ∧ (p3 ∨ p3)) → (p3 → p1)) ∨ (((p3 ∧ (p5 → ((True ∧ p3) ∧ p5))) → p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44022924624085932732889055360 : (((((p4 → ((p3 ∨ p2) ∨ p1)) ∨ ((p3 ∧ (p5 → (p3 ∧ (p4 ∧ False)))) ∨ ((p4 ∧ p2) ∨ (p3 ∧ True)))) → (p3 → False)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300261616296419304327378687003 : (False ∨ ((p4 ∧ (p3 ∧ ((True ∨ (((p2 ∨ p1) ∨ ((True → ((p1 ∨ (False ∨ True)) → p5)) → p2)) → p4)) ∨ (True → p2)))) → (p5 → p5))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136891946729881774525203520901 : (((p3 ∨ p3) ∨ ((False → p2) → (p3 ∨ ((((p1 → (p4 ∨ p2)) → (p5 → (p4 ∧ p1))) ∨ (p3 ∨ p4)) ∧ False)))) ∨ ((p4 → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178335403994646492424969966084 : (((((p1 ∨ p2) ∨ p2) ∨ (p3 ∨ (p1 ∨ (True ∨ p5)))) ∨ (p4 ∧ p4)) ∨ ((True ∨ (p4 → True)) ∧ (True → ((p3 ∧ False) ∨ (p2 ∨ p4))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45421138928620186249981437275 : (((p5 ∧ (p4 → ((((False ∨ ((p5 ∨ (p5 ∨ p2)) ∧ p5)) → ((p2 → p1) ∧ (p3 → True))) ∨ (p4 → (p5 ∧ p4))) ∨ p3))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173118162554969348089245442253 : ((p2 ∨ (((p2 → (p1 ∨ (p3 ∧ False))) ∨ p4) ∧ ((p2 ∧ p5) ∧ (p4 ∨ p1)))) ∨ (False → ((p5 → False) ∧ ((p3 ∨ True) ∨ (False ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611010210710214864336896598161 : (((((((p4 ∨ ((p1 ∧ True) ∧ True)) ∨ p4) ∧ (p5 ∨ (True ∧ ((p3 ∨ (p2 ∧ ((p2 ∨ (p1 → True)) → p5))) ∨ p2)))) → p5) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147271255739824020129508105254 : (((((((p3 ∧ ((p3 → ((p4 ∧ p4) → p1)) ∧ p4)) ∧ p5) ∧ p5) ∨ ((True ∧ p3) ∨ True)) ∨ p4) ∨ False) ∨ (((p4 ∧ p2) ∧ True) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_151156811741579519897520941120 : ((((False ∨ ((p2 → (True ∧ (p5 ∨ (p5 ∨ p4)))) ∨ (p2 ∨ (p3 → False)))) ∨ ((True ∨ p3) ∨ p1)) → False) → (p3 ∨ ((p1 → p5) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ ((p2 → (True ∧ (p5 ∨ (p5 ∨ p4)))) ∨ (p2 ∨ (p3 → False)))) ∨ ((True ∨ p3) ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148351855218980981620600163693 : ((((p2 ∨ p3) → (((p3 ∨ p5) ∨ (p4 ∧ p1)) ∨ ((p4 ∧ p5) ∨ p5))) ∧ (((p4 ∨ p3) → False) ∨ True)) ∨ ((p5 → (p1 ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20790845991406575070276436132 : ((((((p3 ∨ (p1 ∧ True)) ∧ (True ∧ True)) ∧ (p5 ∨ p1)) ∨ p5) ∨ (False → (p5 ∧ (((((False ∨ p2) ∨ p5) ∨ p1) → p2) ∨ p5)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_59511485528593584011896393163 : (((p2 → p1) ∨ (p2 ∧ ((p3 ∧ (p1 ∧ (((((True ∧ p4) ∨ (p2 ∨ (p2 → p1))) ∧ (True ∧ p5)) ∧ p4) ∨ p4))) ∧ (p1 ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148519970683052166977464225479 : ((((True ∧ ((p2 → ((False → p1) ∨ (p2 → p4))) ∧ p4)) → p1) → ((p4 ∧ (p2 ∨ p3)) ∧ (p3 ∨ True))) ∨ (False → (p1 ∧ (p2 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138707476770425018535021670927 : (((((True → True) ∧ (((True ∧ True) ∨ p4) ∨ p5)) ∨ (p2 ∧ (p4 ∨ (p5 ∧ (p3 ∨ ((True → p4) → True)))))) ∧ p2) → ((p1 ∨ True) ∨ p2)) := by
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
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712707727234395164477067979347 : (((((p3 → p5) ∧ (False → (True ∨ False))) ∨ ((((True ∧ p3) ∨ (p1 ∨ ((True → False) → p2))) → (p2 ∧ True)) → (p5 ∧ (p3 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316902209290931392509381353249 : (p3 ∨ (p1 → (p2 → ((p1 → (p1 ∧ (p1 → ((((False → ((p5 ∧ p1) ∨ p3)) ∨ (((p3 ∧ p4) ∨ True) → p1)) → p3) ∨ p2)))) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56952869202900562079671062139 : (((p1 ∨ (p5 → p2)) ∧ (((p3 ∧ (False ∧ (False ∧ (p5 → ((False → p4) → ((p1 → ((False → p1) ∧ p2)) ∨ p5)))))) ∧ False) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135306783660317434949496756300 : (((((p3 ∧ (p5 → (p2 → ((((False ∨ True) ∧ (False ∧ p4)) ∨ p2) ∧ p3)))) ∨ p3) → False) ∧ (p1 ∧ (p4 → False))) ∨ (False → (p1 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250838450887152200640296380192 : ((p1 → p2) ∨ (((p3 ∨ True) ∧ p5) ∨ (((True → False) ∨ (p3 ∧ p2)) ∨ (((True ∧ False) → p3) → ((True ∨ p4) ∧ ((p2 ∨ True) ∨ p1)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46812638074385488106140826166 : (((((p2 ∧ (p5 → (p3 ∨ (((p5 → ((p1 ∧ p2) ∨ p5)) ∨ ((p5 → p1) ∧ p5)) ∧ (p2 ∧ False))))) ∨ p3) ∧ p1) ∨ (False → False)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181072468743539954273774760469 : (((p1 ∨ p5) → ((p1 ∧ (False → ((p5 → p3) → (p2 ∨ p1)))) → p1)) → (((((p2 → p5) ∨ p1) ∧ (p3 → (p2 → p2))) ∧ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229039496093001153329594452224 : ((p5 ∨ (p1 ∨ p3)) ∨ (((((((p4 ∧ (p1 ∨ p4)) ∨ True) → p1) ∨ True) ∨ True) → (((((p3 → p4) ∧ p1) ∧ p4) ∨ True) ∨ p2)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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
theorem thm_5_vars_164472325546285936433828133514 : (((((p2 ∧ (((False ∧ p5) ∨ (p5 ∧ p4)) → p2)) ∨ ((p4 → False) → p3)) ∨ False) ∧ p4) ∨ ((p1 → (p1 ∨ (p4 → (False ∨ False)))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781759611092297861912816935175 : (((p2 ∨ (p5 ∨ (((p5 ∨ p3) → ((((True ∧ False) ∧ (True ∧ True)) ∧ (p1 → p5)) ∨ p1)) ∨ ((p1 ∧ ((p4 ∧ p4) ∧ p1)) → p1)))) ∨ p4) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160506067368918335496237185356 : ((((p5 ∨ p1) ∨ (((True ∧ p2) ∨ (p4 → (p2 ∨ p1))) ∨ p1)) ∧ (p4 ∧ (p5 ∨ (p5 ∧ p3)))) → (((p3 ∨ True) ∨ p2) ∨ (True → p3))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h3.left
      let h7 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h3.left
      let h14 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Conjunctions on the left can always be decomposed.
        let h24 := h3.left
        let h25 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h23
        case inr h27 =>
          -- Conjunctions on the left can always be decomposed.
          let h28 := h27.left
          let h29 := h27.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h23
      case inr h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h3.left
        let h32 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h33 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h34 =>
          -- Conjunctions on the left can always be decomposed.
          let h35 := h34.left
          let h36 := h34.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h36
    case inr h37 =>
      -- Conjunctions on the left can always be decomposed.
      let h38 := h3.left
      let h39 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h40 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h41 =>
        -- Conjunctions on the left can always be decomposed.
        let h42 := h41.left
        let h43 := h41.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h43



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_442949900686514143808686979115 : ((((((True ∧ (p5 ∧ (((True ∧ (p3 ∧ p5)) → (p4 ∧ p2)) ∨ (p2 ∧ (p3 ∧ p5))))) ∨ p3) → (p2 ∧ p5)) ∨ (p5 ∨ (False ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48315951589172904636954534440 : (((False ∨ ((p5 → (p1 ∧ (p4 ∧ p1))) ∧ (p2 ∧ ((False → ((p1 ∨ True) ∧ ((p5 ∧ p2) ∨ (p2 → p1)))) ∧ True)))) → (False ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147738786430594929437431578759 : ((((((p5 → p2) ∧ True) → True) ∨ ((p2 → p4) ∧ (p4 ∨ (p1 ∧ (((p5 ∧ p4) ∧ p5) → p4))))) → p1) ∨ (p1 → (p3 → (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639839103663131213506795373677 : ((((((p4 ∨ True) ∨ p2) ∨ (p2 ∧ (((((p4 ∧ (p1 ∧ (p1 ∨ p5))) ∧ p1) ∨ (False → p1)) → ((p2 ∧ True) → p2)) ∨ False))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149519347864450362201442188324 : ((p1 ∧ (False ∧ (False ∧ ((p3 ∨ ((p5 ∧ (((p2 ∨ (p2 ∧ (p1 ∧ False))) ∨ False) ∧ p2)) ∧ p4)) ∧ p3)))) ∨ ((p3 ∨ (p3 → p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51433173230574302443654436688 : (((((p4 ∨ (p5 ∧ (p5 → p1))) ∨ (False ∨ ((p4 → p1) → (p1 ∨ p5)))) ∨ (p2 ∨ p3)) → ((p5 ∨ (p1 ∨ p5)) → (p2 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114842733965866039870814163225 : ((((p5 ∨ (((p4 ∧ p2) → (p5 → (True ∨ p3))) ∧ (p2 ∨ p3))) ∧ False) ∨ (p2 ∨ (((True ∧ p1) ∧ False) → (p2 ∨ True)))) ∨ (p3 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750126918100910215104894729074 : (((True ∧ ((True → ((p5 → True) → (p3 ∨ ((p3 → (p1 ∧ ((False ∨ (p5 ∨ ((True ∨ (p1 ∧ p2)) ∨ p2))) ∨ p5))) → p2)))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63395713612074139777211294634 : ((p5 ∧ (p2 ∨ (((p5 → p4) ∨ (((((p1 ∧ (p4 → p5)) → p5) ∨ p2) → ((p5 → False) → (p4 ∨ p2))) ∨ p4)) ∨ (True ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602811651875094974401573331890 : ((((p1 ∨ ((((p2 ∧ ((True ∧ (p3 → p2)) ∨ ((((False ∨ False) ∧ p5) → True) ∧ (True ∧ (p3 ∧ p1))))) ∨ True) ∨ False) ∧ False)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715554212648588307126969341 : ((((False ∨ ((p5 ∧ (p4 → p5)) ∧ True)) → True) → ((p5 → ((p3 ∧ (((False ∧ (p5 ∧ p1)) ∧ p2) ∧ p1)) ∨ True)) ∨ p4)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788150974831280231522050499023 : (((p5 ∨ (((True ∨ (p5 ∨ (p1 ∨ (False ∧ (True → p4))))) ∧ (((p4 → (False ∧ False)) ∨ ((p2 ∧ True) → (p2 → p3))) ∨ False)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_889864023317770051939527254871 : (((((p2 → p1) ∨ (((p4 → ((p1 ∨ (False ∨ ((((p5 ∧ (True → p5)) ∨ p1) ∧ p2) ∨ p4))) ∨ p5)) ∧ False) ∨ True)) → (True → p2)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 → p1) ∨ (((p4 → ((p1 ∨ (False ∨ ((((p5 ∧ (True → p5)) ∨ p1) ∧ p2) ∨ p4))) ∨ p5)) ∧ False) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730205623919674560407389211789 : (((((False → p3) → True) → (p5 → (p2 ∨ (((p1 → (p4 ∧ (p2 ∨ (p2 ∧ p5)))) ∨ True) ∨ (((p2 ∨ (False ∧ p2)) ∨ p2) ∨ p4))))) ∨ p3) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682102886037138801925700142139 : ((((((((p4 → (True → True)) ∨ False) ∨ (p5 → ((p3 ∧ p3) → (p5 ∧ p2)))) ∨ p3) → False) ∧ (((p1 ∨ p3) ∧ p1) → (p5 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119034704356342547348375465754 : ((p1 → (((p2 → (((((((True ∨ p4) ∨ p5) ∨ (p3 ∧ (p2 ∧ (p4 ∨ p2)))) → p1) → p4) ∨ p4) ∨ True)) ∨ p5) ∧ p3)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803003482509766341350389594920 : (((p3 → ((((p3 ∨ True) → (((p1 → (p1 → (False ∧ p5))) ∧ (p1 ∧ p2)) ∧ (p5 ∧ p2))) ∨ ((p4 ∧ (p1 ∧ p1)) ∧ p2)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232761902159996326026705926160 : ((p1 ∧ (p5 → p3)) → (((p3 ∨ ((((p4 ∧ (p5 → (p2 ∨ (p2 ∨ p1)))) → (p5 ∧ True)) → p3) → ((p3 ∨ p3) → False))) ∨ p1) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178576846383248361510613489423 : (((p4 ∨ ((p1 ∨ False) → (p5 → False))) ∧ ((p1 ∨ p5) ∧ (True → False))) ∨ ((p1 ∧ ((p1 ∧ p3) ∨ False)) → ((False → p3) ∨ (p5 → False)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619150152397342204558973961040 : (((((p1 ∨ (p1 ∨ p5)) ∨ ((((p1 ∧ ((False ∨ p3) → p1)) ∧ ((True ∧ False) ∧ (p5 ∨ p5))) ∧ True) ∨ (p5 ∧ (p5 → p3)))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215535706948914347618141593060 : ((p4 ∧ (p5 ∨ (p3 ∨ p3))) ∨ ((p2 ∨ (p4 → (p2 ∧ (p4 → ((((p5 → True) → ((False ∧ (p5 ∨ p4)) → p2)) ∨ p5) → True))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173913927972024292089349255712 : ((((p1 ∨ (((((p5 ∧ p2) ∧ p3) ∨ (p4 → p3)) ∧ p3) ∧ p4)) → p1) → False) → ((p3 ∧ (p4 ∧ (False ∨ (p1 ∨ (p4 → p5))))) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h10 : ((p1 ∨ (((((p5 ∧ p2) ∧ p3) ∨ (p4 → p3)) ∧ p3) ∧ p4)) → p1) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Conjunctions on the left can always be decomposed.
          let h16 := h14.left
          let h17 := h14.right
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h18 =>
            -- Conjunctions on the left can always be decomposed.
            let h19 := h18.left
            let h20 := h18.right
            -- Conjunctions on the left can always be decomposed.
            let h21 := h19.left
            let h22 := h19.right
            -- One of the premise coincides with the conclusion.
            exact h9
          case inr h23 =>
            -- One of the premise coincides with the conclusion.
            exact h9
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h24 := h1 h10
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
      have h26 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h25, we can now drive its conclusion.
      let h27 := h25 h26
      -- One of the premise coincides with the conclusion.
      exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318204070114148195155340140906 : (p4 ∨ (((True ∧ ((False ∨ True) → ((False ∧ (True ∨ (p4 → False))) ∧ p4))) ∧ ((True ∧ p3) → (p3 ∨ (((p1 → p3) → p2) ∨ p2)))) → p3)) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348005722617985331190729070157 : (p3 → ((False ∧ p1) ∨ ((((p5 ∧ p3) ∧ True) ∧ False) ∨ (p1 → ((p3 ∨ p4) ∧ ((p4 ∨ (True ∧ p1)) → (p3 → (False ∨ (p2 ∨ True))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233888173537520241008441781805 : ((p4 ∨ (p2 ∨ p5)) → ((True ∧ ((p1 ∨ (p2 → ((((p5 → p3) ∧ ((p2 ∧ p2) ∧ p5)) ∨ True) ∨ p3))) ∨ (True ∧ (True ∨ p4)))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
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
    case inr h5 =>
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134357665382951921769585644932 : (((False ∨ ((((p3 ∨ (p4 → (p4 ∧ (True ∧ False)))) → True) ∧ p3) ∨ (((False → (p3 ∧ p5)) → True) → p3))) ∨ p1) ∨ (p4 → (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597150997554710656870121977164 : (((((((p1 ∨ p3) → p3) ∧ p4) ∧ ((((p5 ∨ p4) ∧ False) → False) → (((p5 ∧ (p1 → ((True ∧ p4) → p1))) ∧ p3) ∧ p1))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113600424848523485745759189709 : (((False ∨ (p2 ∧ ((True ∨ p4) ∧ ((p5 ∨ p1) ∨ ((((p5 → p2) ∨ True) ∨ False) ∨ ((True ∧ p4) → p3)))))) ∨ (p4 ∨ p3)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53701720607426768953341205192 : (((True ∨ (True ∨ (((p1 → p2) → False) ∧ (p1 → True)))) ∧ ((p4 ∧ ((p2 ∨ (((True ∧ (p1 ∧ p2)) → p3) ∨ p1)) → p4)) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



