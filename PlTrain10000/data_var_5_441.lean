variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606237738831642824773878203976 : (((((((p5 ∨ p1) ∨ ((p2 ∧ ((((p1 ∨ ((False → p4) → True)) → p4) → ((p2 → p2) ∨ p2)) → p1)) ∨ True)) ∧ p3) ∧ p3) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_46934213033959701151138515460 : ((((False ∧ (p2 ∨ (p5 ∨ (p5 ∧ ((((p3 → True) → True) → ((p5 ∨ p1) ∧ ((True → p2) → p2))) → p2))))) ∨ False) ∨ (False → p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134984374541049995547117482601 : ((((p3 → True) ∧ ((((False → p4) → p1) ∨ ((p2 ∧ p5) → True)) ∧ (p3 ∧ ((p2 ∨ p1) ∧ False)))) ∧ (p5 ∨ True)) ∨ (p3 ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119318187322752337381143352289 : ((p3 → ((((True → ((p2 ∨ (p5 ∨ (p5 → (p1 → p2)))) → True)) ∨ (True ∧ p5)) → p1) ∨ (True ∧ ((p5 ∧ p2) → p2)))) ∨ (p3 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46311401022428488628677277345 : (((((((p1 ∧ True) ∧ (p4 ∨ p4)) ∧ (p3 ∨ True)) ∧ (((p2 ∨ p5) ∧ p2) ∧ p2)) ∧ (((p5 ∨ p4) ∨ True) ∧ False)) ∧ (p2 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135622098066316451735484356802 : (((p4 → ((True ∧ (False ∧ ((((p1 → (p2 ∨ True)) ∧ False) ∨ p4) ∧ True))) ∧ p1)) ∨ (((p3 → True) → True) ∧ p5)) ∨ ((p1 → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139926926851220285672735301923 : ((((p3 → ((p5 ∧ p1) → (p5 → False))) ∧ (((p4 ∨ p1) ∧ ((True → (True → p1)) ∧ p4)) ∨ p5)) ∧ (p5 ∧ p4)) → (False ∨ (p2 ∨ p5))) := by
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
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h3.left
      let h13 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h8.left
      let h16 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h3.left
      let h18 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h3.left
    let h21 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319070314325475355083767767602 : (p4 ∨ (((((p2 ∨ p4) ∨ (p4 ∨ ((True ∨ ((True → p2) ∨ (False ∧ True))) ∨ (p4 ∧ p5)))) ∨ p4) ∧ p2) → ((p1 → False) ∨ (False ∨ True)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h13 =>
            -- Disjunctions on the left can always be decomposed.
            cases h13
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
              -- False on the left can always be used.
              apply False.elim h16
        case inr h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257706970310235502251334430328 : ((p3 ∨ p3) → ((p1 → False) → ((p3 ∧ ((p4 ∧ ((p5 ∨ (True → p1)) ∧ p4)) ∨ (p1 → (False → False)))) ∨ (False ∧ (p1 → (p5 ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659703075417808143424681204506 : ((((((p1 → True) ∧ ((((p2 ∨ (p3 ∨ p1)) → p5) ∨ ((p1 ∨ (p5 ∨ ((False ∧ p1) ∨ p1))) → p2)) → p1)) ∧ True) → (p3 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53217331065113267209918929441 : (((((((p4 → True) → p4) ∨ p4) → True) → (p1 ∨ (True ∧ p3))) ∨ (((False ∨ ((p1 ∨ p2) ∧ True)) → ((False ∧ p1) ∨ False)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157062968947785864041145438386 : (((p5 ∧ ((p4 → True) ∧ (p4 → ((((p4 ∧ p5) ∨ (p2 → p3)) → (p1 ∧ p5)) ∧ p3)))) ∨ True) ∨ (((p3 ∨ True) → True) ∧ (False → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666065847292842324644655239243 : ((((((p4 ∨ (((((p2 → p1) ∨ (p3 ∧ ((p5 ∨ False) → p5))) ∧ p2) ∨ p2) ∧ True)) ∨ p3) ∧ (p4 ∨ p3)) ∧ ((p5 ∨ p3) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_422320102684382932853522536747 : (((((p5 → (((p2 ∨ ((p5 → ((((True ∨ True) → (p1 ∨ True)) ∧ (True → p1)) ∧ p4)) ∧ p4)) ∨ True) ∨ p5)) ∨ p3) ∧ (p1 ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53086773909558779683230633619 : (((False ∨ (((p5 ∧ False) ∧ p3) ∨ (p5 ∧ ((p4 ∧ p1) ∨ p5)))) ∧ ((p2 → (((False ∧ p1) ∧ (False → p5)) ∧ (p3 ∧ p1))) → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733338380526956188775184025632 : ((((p3 ∧ p5) ∧ (p5 ∨ ((((p2 ∧ True) → False) ∧ (((((True → ((p5 ∨ (False ∨ p3)) → p3)) ∨ p4) → p2) → p1) ∨ p3)) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669065718258875634620541441341 : ((((((p3 ∧ ((True ∨ (p1 ∧ (p5 ∧ False))) ∨ (p3 ∨ (((p4 → (True ∧ False)) ∨ p5) ∨ p4)))) → True) → False) ∨ (False → (p3 ∧ False))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88900014454168942100704307514 : (((p1 ∨ ((p3 → True) ∨ False)) → ((((p4 ∨ (((p5 ∧ False) ∨ False) ∨ (False ∨ (((p3 → p5) ∨ p3) → p2)))) ∧ p1) ∧ p2) ∧ p5)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ ((p3 → True) ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731405286447753017063117909223 : ((((p5 ∨ (False → p3)) → (False ∨ ((p1 ∧ p1) ∨ (((((p1 ∧ (p3 → (p1 ∧ p2))) ∨ p4) ∧ ((False ∧ False) ∧ p4)) ∨ True) ∨ p3)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53897579321153280952351938770 : (((p2 ∧ ((p5 → ((p5 ∧ (p5 ∨ False)) ∧ p3)) → True)) ∨ ((((p2 ∨ (p3 ∨ (p1 ∨ (p1 → p3)))) ∨ p5) → p5) ∨ (p5 → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48627505158956212284521956797 : ((((p4 ∨ (((p2 ∧ (p4 ∧ True)) ∧ ((p3 → (p2 ∨ (p5 ∨ p4))) ∧ p3)) → p1)) ∧ ((False ∧ p4) ∧ p3)) ∧ (False ∨ (p3 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324583122375244365225946426941 : (p5 ∨ (((p3 ∨ True) ∨ True) ∧ (((((p1 ∨ p1) → p4) ∨ (((p4 ∧ True) → (True ∧ p3)) → False)) ∨ (((p3 ∧ p2) ∨ p1) ∧ p4)) ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248462246911317194149258092857 : ((p2 ∨ p5) ∨ (((p4 ∨ ((p5 ∨ p3) → (p5 ∨ p3))) ∧ ((True → False) ∧ p5)) ∨ ((p3 → (p5 ∧ (True → True))) → (p3 → (p3 ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784461937522328304082385304 : (((p2 ∧ p2) → (((((p4 ∧ (((False ∨ p5) → p3) → True)) → ((p4 → p5) → p4)) → p3) → (p1 ∧ (p3 ∧ False))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67958330527587018878971222480 : ((p2 → ((((p5 → p1) ∧ True) ∨ p2) → (((p1 → False) ∨ ((p2 ∧ ((p4 → True) ∨ p1)) ∧ (((p3 → p1) ∨ p2) → p4))) ∨ True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156862965154590589888317461615 : (((((((p3 ∧ (p3 → p4)) ∧ p3) ∨ ((p5 → p1) ∧ p5)) ∧ ((p3 → p3) → p2)) ∧ p5) ∨ True) ∨ ((False ∨ ((True → p1) ∧ p3)) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64002609597183181647058820540 : ((False ∨ (((p4 ∨ ((p5 → ((p5 ∧ (p3 → p4)) ∨ ((False → p5) ∧ p1))) → ((p4 ∨ p4) ∨ p4))) ∨ (p3 → p4)) ∧ (p3 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347409713624849014958040348812 : (p3 → (((True ∧ (False → (p3 ∨ p4))) ∨ (p3 ∨ True)) → ((((p2 ∨ (p1 → p1)) → (p4 → (p5 → p1))) ∨ True) → (p4 → (p2 ∨ True))))) := by
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
    cases h2
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180904801204317116347793935861 : (((False ∨ (p2 ∨ True)) → (((p4 ∧ p3) ∧ p3) ∧ (p2 ∧ (p4 → p2)))) → (p5 ∨ (p4 ∧ ((((p1 ∨ p3) ∨ p3) → False) → (p4 ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ (p2 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (False ∨ (p2 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- One of the premise coincides with the conclusion.
  exact h12
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h13 : (False ∨ (p2 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h13
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615084610136488939350645610386 : (((((p3 → (p2 ∧ (((p1 → p2) ∧ ((p1 ∨ p5) ∧ p1)) → (False → (p1 → (True ∨ p2)))))) → (p1 ∧ ((p1 → p1) → True))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609495558463898931834081924453 : (((((p1 ∧ (((((p3 ∧ (True ∧ True)) ∨ p3) → ((p5 ∧ p2) → p3)) → p1) ∧ (p5 → (p4 ∧ (False ∧ (True ∨ True)))))) ∨ p4) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_748697105981782713042936775497 : ((((p3 → p4) → ((p2 → ((((p2 → (p2 → (p2 ∨ p3))) → (p1 ∨ (True ∧ False))) ∨ (p2 ∧ (p3 → p5))) ∧ (p2 → p1))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623751842009754590370426399148 : ((((p1 ∨ ((((p2 ∨ ((p5 ∨ (p1 ∧ False)) ∧ True)) → p1) ∧ (p2 ∨ ((p4 ∨ False) ∧ False))) ∧ ((p2 ∨ False) ∧ (p2 ∧ p5)))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340864033471707910221801235995 : (p2 → ((((True ∨ ((p5 → ((((p4 ∨ p2) ∧ p2) ∨ False) → p2)) → (p5 ∧ (p1 → p4)))) → False) ∨ ((p2 ∧ (False ∧ True)) → False)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133866723187571298422723047869 : (((p2 ∧ (p3 → (((p4 ∨ ((((False ∧ p5) ∧ False) → False) ∨ ((p4 ∧ False) ∨ (p4 ∧ p2)))) ∨ p5) → p5))) ∧ p5) ∨ (False → (p5 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351387493096893701864971451416 : (p4 → (((False ∧ (p4 → (((p5 ∨ p4) → ((p1 → p2) ∨ (((p5 ∨ p1) ∨ p1) ∨ True))) ∧ False))) ∧ p2) ∨ ((p4 ∧ (True ∨ p5)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157519477969923036434696578195 : (((p5 ∨ (((((False ∧ (p5 ∧ p4)) → p2) → ((p2 ∨ p5) ∧ p1)) ∧ p3) ∨ p1)) ∨ (p2 ∨ p2)) ∨ ((False ∨ ((False ∧ p1) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68419127240811927809587531250 : ((p3 → ((p3 ∧ False) ∨ (((p2 ∧ p4) ∧ p5) ∧ (True ∧ ((True ∧ ((p2 → ((True ∧ p1) ∧ (p1 ∨ False))) ∧ (p1 ∧ p5))) → p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662491533763121456755134980913 : (((((p1 ∨ (p3 ∨ ((p3 ∨ p4) ∨ p2))) ∧ (p2 ∧ ((p2 → p4) ∧ (p3 ∧ (p3 ∧ (((p2 ∨ p4) ∨ p3) → p4)))))) → (False ∨ p3)) ∨ p1) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h3.left
      let h16 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h3.left
          let h27 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h28 := h27.left
          let h29 := h27.right
          -- Conjunctions on the left can always be decomposed.
          let h30 := h29.left
          let h31 := h29.right
          -- Conjunctions on the left can always be decomposed.
          let h32 := h31.left
          let h33 := h31.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h32
        case inr h34 =>
          -- Conjunctions on the left can always be decomposed.
          let h35 := h3.left
          let h36 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h37 := h36.left
          let h38 := h36.right
          -- Conjunctions on the left can always be decomposed.
          let h39 := h38.left
          let h40 := h38.right
          -- Conjunctions on the left can always be decomposed.
          let h41 := h40.left
          let h42 := h40.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h41
      case inr h43 =>
        -- Conjunctions on the left can always be decomposed.
        let h44 := h3.left
        let h45 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h46 := h45.left
        let h47 := h45.right
        -- Conjunctions on the left can always be decomposed.
        let h48 := h47.left
        let h49 := h47.right
        -- Conjunctions on the left can always be decomposed.
        let h50 := h49.left
        let h51 := h49.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h50
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55428588959884168561011587535 : ((((p1 → (p1 → (p3 ∧ p5))) ∨ p1) → (p5 ∨ (p2 ∨ (((p3 ∨ (p1 → p2)) ∨ ((p4 → p2) → ((p5 → p1) → True))) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178936344793390916121361396980 : (((False ∧ p2) ∨ (((p1 → (p5 ∧ (True ∨ (p1 → p2)))) ∨ p2) ∨ p2)) ∨ (((p3 ∨ p5) ∨ True) ∧ ((False ∨ False) ∨ (True ∨ (p3 → p1))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188102172904967532309755320359 : ((((((p1 → p3) ∧ p3) → (p4 ∨ False)) ∧ True) ∨ True) ∧ (p5 → (p4 ∨ (((p4 → p4) ∨ (((False ∧ p5) → p1) ∨ p5)) ∨ (p1 ∧ p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_186621356602315429905207464078 : ((((True ∧ p4) → ((True → p2) → (p1 ∧ False))) → (False ∨ p4)) → (((True ∧ (p5 → (True ∨ (True → p1)))) → (False ∨ (p2 ∧ p4))) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True ∧ (p5 → (True ∨ (True → p1)))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172867146917946421632804243992 : ((p1 ∧ ((p5 ∨ (((True ∨ p3) ∨ ((False ∨ p5) ∧ (p4 ∨ p5))) → p1)) ∧ True)) ∨ (((p3 ∧ ((True ∨ False) → p5)) → (False ∨ p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339960770013741469805499249160 : (p1 → (p1 → (((p4 ∨ ((p4 ∨ (((p3 ∨ ((True ∧ p1) ∨ p1)) → (p1 → (p2 ∨ (p1 → (p4 ∨ p3))))) ∧ p5)) ∧ p2)) ∨ True) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352502151527977206943876516698 : (p4 → ((p5 → (p1 ∨ p4)) → ((((p3 ∧ ((p5 ∨ p1) → ((p2 → p1) ∨ p2))) ∧ (p3 ∨ (p4 ∨ p1))) ∧ p1) ∨ ((p1 ∨ p4) ∨ p2)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589836663256502922870488694130 : (((((((((p5 ∨ p4) → p3) ∧ ((True ∧ True) → (True ∨ (((p1 → False) ∨ p2) ∧ False)))) ∧ p5) ∧ (p2 ∨ (p2 ∧ p2))) → False) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711599174688087693019038959513 : ((((p2 → ((p1 ∧ (p1 ∧ True)) → p2)) ∧ ((p5 ∧ (((p5 → ((p1 ∨ p4) ∧ (((p3 ∨ p2) ∨ p3) ∧ p5))) → p5) ∨ p2)) ∨ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139577014795627356209074825109 : ((((p3 ∨ (((p2 → p5) ∨ p3) ∨ (p4 ∧ (p3 → (False ∧ (p2 ∧ (True ∨ p3))))))) ∨ ((p1 ∨ True) ∨ False)) → False) → (p1 → (p2 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 ∨ (((p2 → p5) ∨ p3) ∨ (p4 ∧ (p3 → (False ∧ (p2 ∧ (True ∨ p3))))))) ∨ ((p1 ∨ True) ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58476989703643262669227121189 : (((p4 ∨ True) ∧ (p4 ∧ ((((p4 ∧ (False ∨ (p2 → ((p2 ∧ True) ∨ p2)))) ∨ (p5 ∧ p3)) ∨ p5) ∧ ((False ∧ (p3 → p1)) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344934124787104923986742152032 : (p3 → ((((((True → p2) → (((p5 → p1) ∧ p4) ∧ ((p1 ∨ ((False → ((p5 ∧ False) → p1)) ∧ p1)) ∧ p4))) → False) → False) ∨ True) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258762650578461183785391490803 : ((True → False) → (((p5 ∧ ((p5 ∧ p4) ∨ ((False ∨ (((p1 → (p1 ∨ ((p4 → p1) → p3))) ∧ False) ∧ p5)) ∧ (True → p2)))) ∧ p5) ∨ p2)) := by
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
theorem thm_5_vars_64671895536153595495054763906 : ((p1 ∨ (p2 ∨ (((p5 → False) ∧ (((((True ∨ p1) ∧ p4) ∧ True) ∧ p3) → p2)) ∨ ((p1 → p2) ∨ (p4 → (p4 ∧ (p5 ∨ p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634472107991498703231772091632 : (((((((p5 ∧ (p4 → False)) ∨ (((p3 → p5) ∧ (p5 ∧ (True ∨ p4))) ∨ p4)) ∨ (False ∨ (False ∧ True))) ∧ (False → (p5 ∧ p3))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152033831643069893633306401566 : ((((p2 ∧ p1) ∧ (((p4 ∧ p4) ∨ (p1 ∨ False)) ∨ p5)) ∧ (((((p2 ∨ p2) → p5) ∨ p2) ∨ False) ∨ p3)) → ((p4 → p3) ∨ (False → p4))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h15
            -- False on the left can always be used.
            apply False.elim h15
          case inr h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h17
            -- False on the left can always be used.
            apply False.elim h17
        case inr h18 =>
          -- False on the left can always be used.
          apply False.elim h18
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- False on the left can always be used.
        apply False.elim h20
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h24 =>
            -- Disjunctions on the left can always be decomposed.
            cases h24
            case inl h25 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h26
              -- False on the left can always be used.
              apply False.elim h26
            case inr h27 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h28
              -- False on the left can always be used.
              apply False.elim h28
          case inr h29 =>
            -- False on the left can always be used.
            apply False.elim h29
        case inr h30 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h31
          -- False on the left can always be used.
          apply False.elim h31
      case inr h32 =>
        -- False on the left can always be used.
        apply False.elim h32
  case inr h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h34 =>
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h35 =>
        -- Disjunctions on the left can always be decomposed.
        cases h35
        case inl h36 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h37
          -- False on the left can always be used.
          apply False.elim h37
        case inr h38 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h39
          -- False on the left can always be used.
          apply False.elim h39
      case inr h40 =>
        -- False on the left can always be used.
        apply False.elim h40
    case inr h41 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h42
      -- False on the left can always be used.
      apply False.elim h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137241581876002334239625642232 : ((p1 ∧ ((p3 ∧ ((((False ∧ p3) → True) ∧ p4) ∨ (((True ∧ p4) ∨ p1) ∨ p3))) ∨ ((False ∨ True) ∨ (p4 ∧ p5)))) ∨ ((p2 ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64267753779239493117450734170 : ((False ∨ (True → ((((False ∧ (p2 ∨ (((p1 ∨ ((p3 ∨ (False ∨ p4)) ∧ (p3 ∨ (p1 → False)))) ∨ p1) ∨ p2))) ∨ False) → True) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667624158430634733838912423686 : ((((p2 ∧ (p4 ∧ ((p1 ∨ ((p2 ∨ p5) ∨ True)) → (((p4 → p4) ∧ (p5 ∨ p2)) ∧ (p5 ∧ (p2 ∧ p5)))))) ∧ (True → (p4 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166437516061433160563218875565 : ((p1 ∨ (p4 → ((((p3 → p4) → (True ∨ p1)) ∧ (p2 ∧ p1)) ∧ (p3 → (p2 → False))))) ∨ ((False ∨ (True ∨ (True ∧ True))) ∨ (p5 → False))) := by
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
theorem thm_5_vars_184652531157603040197408827619 : ((((p2 ∨ (p2 ∧ (False → p2))) ∨ p5) ∨ (p5 ∧ (p4 → p5))) ∨ (p1 ∨ ((p2 ∨ ((((p3 ∧ False) ∧ (p3 ∨ p3)) ∧ p4) ∨ p2)) → p2))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53140469114079404131054484458 : ((((p5 ∧ ((((p3 → (p1 ∨ p5)) ∨ p3) ∨ p3) ∨ False)) ∧ p4) ∨ ((p2 ∧ ((p1 ∧ True) ∧ True)) → ((p4 → p5) → (True ∧ p2)))) ∨ p2) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218846408309042890983642337232 : ((p2 ∧ ((p5 ∧ p5) → True)) → ((p5 → ((((p3 ∨ (((True ∨ (p5 ∧ p1)) ∨ p4) → False)) ∧ (p2 → p3)) ∨ p3) → p4)) ∨ (p5 ∨ True))) := by
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
theorem thm_5_vars_116493762266449802391168913069 : (((p3 ∧ True) ∧ (((p4 ∧ (p4 → (True ∨ (p1 ∨ (p4 → p1))))) ∧ (p2 ∨ p5)) ∧ (p1 ∨ (False → (p1 → (True ∧ True)))))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152221418685611501502699717235 : ((((True ∨ p2) → (p5 ∧ (p2 ∧ p3))) ∧ ((p4 ∨ (((p2 → p4) ∧ (p1 ∧ p3)) ∨ (p1 → p4))) ∨ p3)) → (((p2 ∨ p1) ∨ p4) → p3)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h1.left
      let h6 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h9 : (True ∨ p2) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h10 := h5 h9
          -- We need to get the right conjuct of h10 based on <expert-advice>.
          let h11 := h10.right
          -- We need to get the right conjuct of h11 based on <expert-advice>.
          let h12 := h11.right
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Conjunctions on the left can always be decomposed.
            let h15 := h14.left
            let h16 := h14.right
            -- Conjunctions on the left can always be decomposed.
            let h17 := h16.left
            let h18 := h16.right
            -- One of the premise coincides with the conclusion.
            exact h18
          case inr h19 =>
            -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
            have h20 : (True ∨ p2) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h5, we can now drive its conclusion.
            let h21 := h5 h20
            -- We need to get the right conjuct of h21 based on <expert-advice>.
            let h22 := h21.right
            -- We need to get the right conjuct of h22 based on <expert-advice>.
            let h23 := h22.right
            -- One of the premise coincides with the conclusion.
            exact h23
      case inr h24 =>
        -- One of the premise coincides with the conclusion.
        exact h24
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h1.left
      let h27 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
          have h30 : (True ∨ p2) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h26, we can now drive its conclusion.
          let h31 := h26 h30
          -- We need to get the right conjuct of h31 based on <expert-advice>.
          let h32 := h31.right
          -- We need to get the right conjuct of h32 based on <expert-advice>.
          let h33 := h32.right
          -- One of the premise coincides with the conclusion.
          exact h33
        case inr h34 =>
          -- Disjunctions on the left can always be decomposed.
          cases h34
          case inl h35 =>
            -- Conjunctions on the left can always be decomposed.
            let h36 := h35.left
            let h37 := h35.right
            -- Conjunctions on the left can always be decomposed.
            let h38 := h37.left
            let h39 := h37.right
            -- One of the premise coincides with the conclusion.
            exact h39
          case inr h40 =>
            -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
            have h41 : (True ∨ p2) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h26, we can now drive its conclusion.
            let h42 := h26 h41
            -- We need to get the right conjuct of h42 based on <expert-advice>.
            let h43 := h42.right
            -- We need to get the right conjuct of h43 based on <expert-advice>.
            let h44 := h43.right
            -- One of the premise coincides with the conclusion.
            exact h44
      case inr h45 =>
        -- One of the premise coincides with the conclusion.
        exact h45
  case inr h46 =>
    -- Conjunctions on the left can always be decomposed.
    let h47 := h1.left
    let h48 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h48
    case inl h49 =>
      -- Disjunctions on the left can always be decomposed.
      cases h49
      case inl h50 =>
        -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
        have h51 : (True ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h47, we can now drive its conclusion.
        let h52 := h47 h51
        -- We need to get the right conjuct of h52 based on <expert-advice>.
        let h53 := h52.right
        -- We need to get the right conjuct of h53 based on <expert-advice>.
        let h54 := h53.right
        -- One of the premise coincides with the conclusion.
        exact h54
      case inr h55 =>
        -- Disjunctions on the left can always be decomposed.
        cases h55
        case inl h56 =>
          -- Conjunctions on the left can always be decomposed.
          let h57 := h56.left
          let h58 := h56.right
          -- Conjunctions on the left can always be decomposed.
          let h59 := h58.left
          let h60 := h58.right
          -- One of the premise coincides with the conclusion.
          exact h60
        case inr h61 =>
          -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
          have h62 : (True ∨ p2) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h47, we can now drive its conclusion.
          let h63 := h47 h62
          -- We need to get the right conjuct of h63 based on <expert-advice>.
          let h64 := h63.right
          -- We need to get the right conjuct of h64 based on <expert-advice>.
          let h65 := h64.right
          -- One of the premise coincides with the conclusion.
          exact h65
    case inr h66 =>
      -- One of the premise coincides with the conclusion.
      exact h66



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345655007725560409712798245997 : (p3 → ((p5 ∧ (((((((p4 ∨ (p4 → p2)) → p2) → p1) ∨ p2) ∨ p4) ∨ p5) ∨ (((p1 ∧ (True ∧ p3)) ∨ (p4 ∨ False)) ∧ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173210097179320800562374596115 : ((p5 ∨ ((((p2 ∧ p1) ∨ False) ∨ p3) ∨ ((p3 ∧ True) ∨ (False ∨ (p1 ∨ p1))))) ∨ (((p3 → False) ∨ (p2 ∧ p2)) ∨ (p1 → (False ∨ True)))) := by
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
theorem thm_5_vars_115377983955124017118374144187 : ((((p5 ∧ ((p5 → False) ∧ p2)) → (p1 ∨ True)) ∧ (((((p2 ∧ (False → p1)) ∨ (p1 → p3)) ∧ (p3 → True)) ∧ p2) → p4)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165732266821673794382155577213 : (((((p3 ∨ p3) ∨ True) ∧ p3) ∨ (False ∨ (p3 ∨ ((True ∨ ((p2 ∨ p1) ∧ p5)) → True)))) ∨ (p3 ∧ (((p2 ∧ p1) → (False ∧ p1)) → False))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655363602005301312570791105965 : ((((((p5 → ((((p3 ∧ ((p2 ∧ p3) ∨ (p4 ∧ (True → p2)))) ∨ p3) → (p5 ∧ False)) ∧ p1)) ∨ p1) ∨ (p2 ∨ p3)) ∨ (p1 ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60215615872711360841658144556 : (((True → False) → (p4 → (p1 ∨ (p2 ∧ (((p1 ∧ ((p5 ∨ ((p5 ∨ p5) → p2)) ∨ ((True → p5) → (p3 ∧ p1)))) ∧ p1) → False))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59882188590472074613136721653 : (((p4 ∧ p4) → ((p2 → False) ∨ (((p1 → p2) ∧ (((p5 ∨ (p4 ∨ False)) ∧ True) ∨ (p3 ∨ p3))) → ((p5 ∨ (False ∨ p4)) ∨ False)))) ∨ p1) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613934324469680269975036431307 : (((((((p3 ∨ ((p1 → ((p1 → (p2 ∧ p3)) ∨ p2)) → p5)) ∨ ((p1 → p5) ∨ True)) → (p5 ∨ p1)) ∨ ((p2 → True) ∨ p2)) ∨ p3) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199773441319404821870336007880 : (((p3 → ((p2 ∨ p5) ∨ (True ∨ False))) → False) → (True → (((p4 → (p4 → p5)) ∨ p2) ∧ ((p4 ∨ (p2 ∧ ((p5 ∧ True) ∨ p1))) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p3 → ((p2 ∨ p5) ∨ (True ∨ False))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p3 → ((p2 ∨ p5) ∨ (True ∨ False))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (p3 → ((p2 ∨ p5) ∨ (True ∨ False))) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h9
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652365233506352998091067662208 : ((((p4 ∧ (((p2 ∧ True) → (((True → (p4 ∧ p2)) → p1) → False)) ∨ (((((True ∨ p2) ∧ p4) ∧ p3) → p3) ∧ p5))) ∧ (p1 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62199067029072705770338039348 : ((p3 ∧ ((((p3 → (p2 ∨ ((p5 ∧ (p3 → p2)) → (False ∧ p5)))) ∨ p5) ∨ (p4 ∨ ((p1 ∨ (p4 → p2)) ∧ (p3 ∧ p5)))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757543739626235611608415315830 : (((p1 ∧ (p2 ∧ (((p2 ∨ ((p4 → (((((False → p2) ∨ False) → False) ∨ p5) ∧ p2)) → p3)) ∨ ((False ∨ p4) ∨ (p3 ∨ p4))) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_23033899069451682834913168769 : ((((p5 ∨ ((p4 → p5) ∧ p1)) ∧ p4) → ((p2 ∧ (((p5 ∨ (True ∨ (((p5 ∨ False) → True) ∧ True))) → (p2 ∨ True)) ∨ p5)) ∨ p5)) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153494628588507970032076283158 : ((p5 ∨ (((p1 ∨ (True → (p3 ∧ p4))) ∧ True) ∧ (((False → p2) → (p2 ∧ False)) ∨ (p3 ∨ (p1 ∧ p3))))) → (p5 ∨ (p3 ∨ (True → p3)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h9 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h10 : (False → p2) := by
          -- Implications on the right can always be decomposed.
          intro h11
          -- False on the left can always be used.
          apply False.elim h11
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h12 := h9 h10
        -- We need to get the right conjuct of h12 based on <expert-advice>.
        let h13 := h12.right
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h18
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h20 =>
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h21 : (False → p2) := by
          -- Implications on the right can always be decomposed.
          intro h22
          -- False on the left can always be used.
          apply False.elim h22
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h23 := h20 h21
        -- We need to get the right conjuct of h23 based on <expert-advice>.
        let h24 := h23.right
        -- False on the left can always be used.
        apply False.elim h24
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h26
        case inr h27 =>
          -- Conjunctions on the left can always be decomposed.
          let h28 := h27.left
          let h29 := h27.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116631527068398069106485946395 : (((p1 → p2) ∧ (p2 → (((((True ∨ (True → (p5 → False))) → ((False → p4) ∧ p1)) ∧ p1) ∧ (p5 ∨ (p1 → p5))) ∧ p4))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654434265082413364136829709237 : ((((((p4 ∧ (p4 ∧ p3)) ∨ (p4 → (True → (((p1 ∨ p5) ∨ (p2 → p2)) → (p1 → (p5 ∨ (p5 ∧ p5))))))) ∨ p2) ∨ (p4 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339726167776393592552785865237 : (p1 → (p4 ∨ (((p2 ∨ p4) ∧ ((p1 ∧ True) → ((((p4 ∨ p4) → p1) ∧ p4) ∨ ((p5 → ((p4 → True) → p2)) ∧ (p5 → True))))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206878590500444909648530763753 : ((((True ∨ (False → p4)) ∧ True) ∧ p4) → (((((((((p3 → p3) ∨ True) ∨ p3) ∧ p4) ∨ (p5 ∧ True)) ∧ p1) ∧ p4) ∧ p3) → (False ∨ p1))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h1.left
        let h15 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h16 := h14.left
        let h17 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h1.left
        let h22 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h23 := h21.left
        let h24 := h21.right
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h1.left
      let h29 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h30 := h28.left
      let h31 := h28.right
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h32 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h33 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
  case inr h34 =>
    -- Conjunctions on the left can always be decomposed.
    let h35 := h34.left
    let h36 := h34.right
    -- Conjunctions on the left can always be decomposed.
    let h37 := h1.left
    let h38 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h39 := h37.left
    let h40 := h37.right
    -- Disjunctions on the left can always be decomposed.
    cases h39
    case inl h41 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h42 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734209825122285570464904416317 : ((((False ∨ False) ∧ (((((True → (False ∧ False)) ∨ (p3 ∨ False)) → ((p5 ∧ ((False → p2) ∧ False)) ∨ False)) ∧ ((p5 → p5) ∧ p4)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136558599063707258053031926562 : ((((p4 ∨ False) ∨ p1) ∨ ((((True → (p4 → ((True → True) → p3))) ∨ ((p5 ∨ False) → (p1 ∧ p4))) → False) → p4)) ∨ (p3 ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87490355298635436382723441000 : ((((p4 ∧ ((False → p3) → p1)) ∧ False) ∨ ((((p4 → p1) → p3) → (p5 ∨ ((p3 → ((p4 ∧ (p4 → p2)) ∧ p3)) ∨ True))) → p4)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (((p4 → p1) → p3) → (p5 ∨ ((p3 → ((p4 ∧ (p4 → p2)) ∧ p3)) ∨ True))) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h8
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68930718783132925458997338277 : ((p4 → (p3 ∨ (p2 ∨ ((p4 → (p5 ∨ ((((False ∧ False) ∨ p4) → p5) ∧ (p2 → (p5 ∧ ((p3 ∨ (True → p1)) ∧ p5)))))) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341042892550599624022311374746 : (p2 → ((False ∨ (((p4 ∧ (p4 ∧ ((((p2 ∧ True) → False) ∨ (p3 ∨ (p4 ∨ p1))) ∧ False))) ∨ False) ∨ ((p1 ∨ (p5 ∧ p1)) ∧ p3))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90919674719658804252896767074 : (((True → False) ∧ ((p4 ∧ ((True ∧ ((p5 → (p1 ∨ True)) → (p2 ∧ ((p5 ∨ p1) → (p4 ∨ ((p3 → p4) ∧ p4)))))) ∧ p1)) → p2)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675651884667645661908842872344 : (((((((p2 ∨ False) ∨ (((p5 → (p3 ∨ p3)) → p2) → ((p2 ∨ False) ∧ p3))) → False) → (p1 → p2)) ∧ (((p2 ∨ True) ∨ p1) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50514471271288581799921115535 : (((((p1 ∧ (False ∨ p4)) ∨ (((p2 ∧ (p2 → p2)) ∨ (((p1 ∨ False) ∨ p3) → p3)) → p3)) ∧ True) → (((p5 ∨ p2) ∧ p1) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165584271512595509927683871104 : (((p5 ∧ (p3 ∨ (p4 ∧ ((p2 ∨ p1) → p3)))) ∨ ((p1 → p2) ∨ (p2 → (p4 ∨ True)))) ∨ (p2 → ((p1 → (p3 ∧ p4)) ∨ (p3 ∨ p3)))) := by
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
theorem thm_5_vars_158361364930314717047252451635 : (((p1 ∨ p3) ∧ (((p3 → False) → True) → ((((((p5 → p5) → False) ∨ p5) ∨ p5) ∧ p1) ∨ p1))) ∨ (False → (p1 ∧ ((p1 → p2) ∨ True)))) := by
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
theorem thm_5_vars_48733724442391530338138775566 : (((((False ∨ False) ∧ p1) ∨ (p1 ∧ ((p1 → (p4 ∧ (False ∧ (((p3 → p1) ∧ (False → p1)) → False)))) → p1))) ∧ (p4 → (p4 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317863212113907637235827560904 : (p4 ∨ (((p1 ∨ p1) ∨ (False ∧ (True → ((((p4 ∨ p1) ∧ (p3 ∧ (False ∨ ((p1 ∧ p1) → True)))) ∧ ((p3 ∧ p3) ∧ p1)) ∨ p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168448302809132799684086611910 : (((True → p3) → (False ∨ (p4 ∧ ((p1 ∨ ((p5 ∨ (p1 ∧ p4)) ∨ True)) ∨ (True → True))))) → (p4 ∨ ((((p3 → p4) → p1) ∨ p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174779107040293488599278714942 : (((True ∨ True) ∧ (p5 ∨ ((p4 ∧ (((p3 → p3) → (p2 ∧ p3)) ∨ p4)) ∧ True))) → ((p5 ∧ p1) ∨ (True ∧ ((True → (True ∧ p2)) → p2)))) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h8 := h6 h7
      -- We need to get the right conjuct of h8 based on <expert-advice>.
      let h9 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h16
        -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
        have h17 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h16, we can now drive its conclusion.
        let h18 := h16 h17
        -- We need to get the right conjuct of h18 based on <expert-advice>.
        let h19 := h18.right
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h21
        -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
        have h22 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h21, we can now drive its conclusion.
        let h23 := h21 h22
        -- We need to get the right conjuct of h23 based on <expert-advice>.
        let h24 := h23.right
        -- One of the premise coincides with the conclusion.
        exact h24
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h26 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h27
      -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
      have h28 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h27, we can now drive its conclusion.
      let h29 := h27 h28
      -- We need to get the right conjuct of h29 based on <expert-advice>.
      let h30 := h29.right
      -- One of the premise coincides with the conclusion.
      exact h30
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- Conjunctions on the left can always be decomposed.
      let h34 := h32.left
      let h35 := h32.right
      -- Disjunctions on the left can always be decomposed.
      cases h35
      case inl h36 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h37
        -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
        have h38 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h37, we can now drive its conclusion.
        let h39 := h37 h38
        -- We need to get the right conjuct of h39 based on <expert-advice>.
        let h40 := h39.right
        -- One of the premise coincides with the conclusion.
        exact h40
      case inr h41 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h42
        -- We want to use the implication h42 based on <expert-advice>. So we show its premise.
        have h43 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h42, we can now drive its conclusion.
        let h44 := h42 h43
        -- We need to get the right conjuct of h44 based on <expert-advice>.
        let h45 := h44.right
        -- One of the premise coincides with the conclusion.
        exact h45



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615680626445377568801609547104 : (((((((p3 ∨ (p5 → False)) → (((False → p4) ∧ p4) ∧ p4)) → (p5 ∨ p5)) ∧ ((True ∨ ((False → (p1 ∨ p4)) → True)) ∧ True)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_300604201203751311107150700434 : (False ∨ ((((p4 ∧ (p1 ∧ p4)) ∨ p4) → (((p2 ∨ (((False → p2) ∨ p2) ∨ (False ∨ False))) ∧ True) ∨ p3)) → ((p4 → (False ∧ True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245811531834185376403468146694 : ((p3 ∧ p3) ∨ (False ∨ (p5 → ((((True ∨ (((p5 ∧ ((p1 ∨ p5) ∧ (p4 ∧ p4))) → (True → (p3 → False))) ∧ False)) → p4) ∨ p1) ∨ True)))) := by
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
theorem thm_5_vars_630691300907038492273159744961 : (((((p1 → ((p1 → p4) ∧ ((((p5 ∧ p3) → True) ∧ (((True → (p4 ∨ (p2 → p2))) → p2) → (p1 → p1))) → p1))) ∨ p2) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



