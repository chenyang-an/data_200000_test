variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720585069678694608525444985090 : ((((((False ∨ False) ∧ p1) → p4) → ((True ∧ (True ∧ True)) ∧ ((p5 ∧ (((False → (False ∧ (p2 ∧ True))) → p3) ∧ False)) ∨ (False → p3)))) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157739529541061045036583127663 : (((((p4 ∨ p1) → (False ∧ (((p4 → False) ∧ True) → p2))) ∧ p5) ∧ ((p1 → (p3 ∧ p4)) ∨ False)) ∨ (False → ((p2 ∧ p2) ∧ (True ∨ p1)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693684203126201455901375869331 : (((((((p4 ∨ p2) ∧ p2) ∧ (p2 ∨ ((False → (False → p4)) ∧ False))) ∨ p2) ∨ (True ∨ (((False ∨ (False ∨ (p3 → p5))) → p2) ∧ p5))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599615112438883044082739001303 : (((((True → False) ∨ ((p5 ∧ p4) ∨ (True → (p5 ∨ ((True ∨ ((((p2 → p3) → p4) → (p1 ∧ p5)) ∧ (p4 ∨ True))) ∨ p1))))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326885362452179658304615174072 : (True → ((((p5 ∧ p4) ∨ (p3 → ((p1 → (((True → p2) ∨ p5) → (p5 ∧ (p2 ∧ (p2 ∧ ((p2 ∧ True) ∧ p4)))))) ∧ p3))) ∨ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702990391982057738368589168760 : ((((((p1 → p4) ∨ False) → ((p5 → False) ∨ (True ∧ p3))) ∨ ((p3 → (p3 ∨ (p1 ∧ ((p2 ∨ False) ∨ (p2 ∧ p1))))) ∨ (p1 ∧ p5))) ∨ p5) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_861352450217346312923155451553 : ((((((True ∨ (p2 ∧ (p1 → (p1 → p4)))) → ((p2 ∧ ((True ∧ p2) ∧ (p4 ∨ True))) → (p5 → False))) ∨ ((False → p1) ∨ p1)) → p1) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True ∨ (p2 ∧ (p1 → (p1 → p4)))) → ((p2 ∧ ((True ∧ p2) ∧ (p4 ∨ True))) → (p5 → False))) ∨ ((False → p1) ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256411308837554127035248376431 : ((False ∨ p3) → ((p2 ∧ ((p4 ∧ True) ∨ (p1 ∨ (p4 → (p5 ∧ ((((True → False) → False) ∧ True) → (p5 ∧ p1))))))) ∨ ((p3 ∨ p3) ∧ True))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47005582158967875769511073312 : (((((p2 ∧ True) ∨ (True ∧ ((p5 ∧ (((((True → True) ∨ ((p4 ∨ p2) ∨ p1)) ∨ p5) ∨ p2) ∧ p5)) ∨ p1))) → p4) ∨ (p1 → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313260901316295372237480423097 : (p3 ∨ ((True ∧ ((p1 ∧ p4) ∧ (((True → ((False ∨ (p4 ∧ ((p3 ∧ (p4 ∨ p4)) ∨ False))) ∨ False)) ∧ (True ∨ (True ∧ True))) ∧ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166680323764813612667816989685 : ((p2 → ((((p1 ∧ p3) ∨ p4) ∨ ((p1 ∧ p2) ∧ p5)) ∨ (((p3 ∨ True) ∧ p2) → False))) ∨ (True ∨ (p3 ∧ (((p2 → p4) → p1) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210391793629331827228337706418 : (((p1 ∨ (p3 ∧ p2)) ∨ True) ∧ (p5 → ((True ∧ p3) ∨ (False ∨ ((p5 ∨ (p3 ∨ (p1 ∧ (((False → (p1 → p1)) → p3) ∨ True)))) ∨ p4))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80250950477744078795781108113 : ((((((((p5 ∧ p4) ∨ p4) ∨ False) ∧ (p1 → (p5 ∨ p3))) ∧ (True → ((p4 ∨ (p1 → False)) ∨ p5))) ∨ (True ∨ False)) → (p5 ∧ p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((p5 ∧ p4) ∨ p4) ∨ False) ∧ (p1 → (p5 ∨ p3))) ∧ (True → ((p4 ∨ (p1 → False)) ∨ p5))) ∨ (True ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51761082879591204208844804770 : ((((p4 → p5) ∨ (p1 ∧ (p5 ∨ ((((p1 ∨ False) ∨ (True → p4)) ∨ p2) ∧ p5)))) ∧ ((True ∨ (True ∧ ((p3 ∨ True) → p5))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148492053275980536255614366918 : (((((False ∨ p5) ∨ ((p5 ∨ False) ∨ p2)) ∨ (False ∨ (p4 → p2))) ∨ (True ∨ (((p5 ∨ True) ∧ p4) → p1))) ∨ (False → (p2 → (p1 ∨ p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156755975702687220994847221673 : ((((p1 ∧ p2) ∧ ((True ∧ ((p4 → p3) → (False ∨ p2))) ∧ (((p5 → False) ∨ p4) ∧ p4))) ∧ p5) ∨ (p5 → ((p5 ∨ False) ∧ (p5 ∨ p2)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300386236210682317995163111915 : (False ∨ ((((p2 → (p5 ∨ p2)) ∧ ((False ∧ p4) → p1)) → ((False → (((p2 ∨ p4) ∨ (False → p5)) → False)) ∧ p3)) ∨ (True ∨ (p5 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44446869300917278669802994295 : ((((((p4 ∧ p2) → (((False → (p4 ∧ p3)) ∨ p5) → p1)) ∨ p2) ∨ (((True ∧ p2) ∧ p4) → (p3 ∨ (p4 ∧ (p3 → p4))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68615226341279936646448002322 : ((p4 → (((p4 ∧ ((((p5 → p1) ∨ (False ∧ p4)) ∨ (True ∧ True)) → p5)) ∨ (((p2 → (p2 ∧ p4)) ∨ p3) → (p5 ∨ p2))) ∨ p4)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744389485365124826654250551420 : ((((p2 ∧ True) → ((p1 ∨ True) ∧ (((p3 ∨ ((p5 → p4) ∨ ((False ∨ True) ∧ ((p3 ∧ (p2 → True)) ∧ p5)))) ∨ (p5 → p2)) ∨ p4))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134909546835263888816346149309 : ((((p3 ∨ (True → (((p4 ∨ ((p4 ∨ p4) ∧ (p1 → p4))) → ((True ∨ p5) → p3)) ∧ p4))) ∧ p4) ∧ (p4 ∧ p5)) ∨ ((p1 → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_457309194204863599565637995205 : (((((((False ∨ p2) → False) → ((True ∨ (((p2 → p5) → (p3 ∧ p1)) ∨ p3)) → p4)) ∨ p2) ∨ (False → (((p1 ∧ False) ∧ p5) ∨ p4))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39224347622165600983669160545 : (((True ∧ (False ∧ (p2 ∧ (p3 → (((p2 ∨ (((False ∨ p3) ∨ ((False ∨ p1) ∧ p5)) ∧ p4)) ∧ ((True → False) → False)) ∧ p3))))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203020079479409506939219017568 : (((p3 ∧ p5) → ((p1 ∨ p3) ∨ p5)) ∧ (((False ∨ (((p1 ∨ p4) ∧ (p5 → p1)) → p5)) ∨ p2) ∨ (True → ((p1 → p4) → (p1 → p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149682503343184336154934605826 : ((p5 ∧ (((((False ∨ (p5 ∧ ((p5 ∨ p2) ∧ p2))) ∧ True) ∧ (p1 → p2)) → ((p5 ∧ p4) ∨ p2)) → p1)) ∨ (((False ∨ True) → p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61048139133663639876246207873 : ((False ∧ (((p5 ∧ (False ∨ ((((((p1 ∨ p5) → True) → False) ∧ p3) ∨ ((p5 ∨ (p1 ∨ p2)) → False)) ∧ p1))) → p2) → (p3 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168175262520135347043212765034 : (((True ∨ (p5 → True)) ∧ (p5 ∨ (((p5 ∨ p5) ∧ ((p1 ∨ p5) ∧ (p2 ∨ p1))) ∧ p2))) → (((p5 ∧ (p4 ∨ True)) ∧ (p1 ∨ p4)) ∨ p5)) := by
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
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h10.left
        let h13 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h11
          case inr h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h11
        case inr h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h17
          case inr h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h17
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h10.left
        let h22 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h24 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h20
          case inr h25 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h20
        case inr h26 =>
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h27 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h26
          case inr h28 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h26
  case inr h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h30 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
      cases h34
      case inl h36 =>
        -- Conjunctions on the left can always be decomposed.
        let h37 := h35.left
        let h38 := h35.right
        -- Disjunctions on the left can always be decomposed.
        cases h37
        case inl h39 =>
          -- Disjunctions on the left can always be decomposed.
          cases h38
          case inl h40 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h36
          case inr h41 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h36
        case inr h42 =>
          -- Disjunctions on the left can always be decomposed.
          cases h38
          case inl h43 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h42
          case inr h44 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h42
      case inr h45 =>
        -- Conjunctions on the left can always be decomposed.
        let h46 := h35.left
        let h47 := h35.right
        -- Disjunctions on the left can always be decomposed.
        cases h46
        case inl h48 =>
          -- Disjunctions on the left can always be decomposed.
          cases h47
          case inl h49 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h45
          case inr h50 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h45
        case inr h51 =>
          -- Disjunctions on the left can always be decomposed.
          cases h47
          case inl h52 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h51
          case inr h53 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h51



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111902937021497582900827368156 : (((((p3 → (p2 → False)) ∨ (((p2 ∧ True) ∨ p2) ∧ (p5 → (p3 → True)))) → ((p4 → (p3 → True)) → (p5 ∨ p3))) ∨ False) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8958475898344385867443926916 : (((((p5 ∧ p2) ∧ (p2 ∨ (((p3 ∧ p5) ∨ ((p1 → p1) ∨ p1)) → (p5 ∧ True)))) ∧ ((p5 ∧ p3) ∧ (p2 → (p2 → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160307977551266373136748509855 : ((((True → (p3 ∨ ((p1 ∧ False) → (p1 ∧ (p2 ∨ False))))) → ((p3 ∨ p3) ∧ True)) → (False ∨ p5)) → ((True → False) ∨ (True → (True ∨ p1)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304858955888924797153798772789 : (p1 ∨ ((((p2 ∨ p5) ∨ (p5 ∨ p2)) ∨ (((p1 ∨ (p5 → True)) → True) ∨ ((p4 ∧ ((p3 ∧ p4) → (True ∨ p1))) → False))) → (p2 ∨ True))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117166889087086279695657976128 : ((True ∧ ((((((p2 → False) ∧ ((p4 → p1) ∧ (p4 ∨ p5))) ∧ p4) → (((p3 ∧ (p4 → p3)) ∧ p2) ∧ p4)) ∨ True) → False)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10170628505131179414065487142 : (((p1 ∨ ((p3 ∨ (((((True ∨ ((p1 ∧ p2) ∧ p2)) ∨ p3) → (False ∨ ((p5 ∧ True) ∨ p3))) → True) → (p5 → p4))) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_309632137609238908156361675741 : (p2 ∨ ((((((p1 ∨ True) → p3) ∧ (p3 ∨ p5)) ∨ p1) → ((True ∧ (p2 ∨ (p5 → (p2 ∨ (True ∨ p5))))) → p5)) ∨ ((True ∧ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350119493624794381506281913058 : (p4 → ((((True → ((p2 ∨ ((p5 → p5) → False)) ∨ p3)) ∨ (False → (p5 ∨ (p5 ∨ p3)))) ∧ (p3 ∨ ((p2 ∧ (False ∨ p3)) → True))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147990980225839423075974186943 : ((((False ∧ ((p3 ∧ ((p2 → False) ∨ (((p5 ∨ (False ∧ p4)) ∨ p4) ∧ True))) → p2)) ∨ p1) ∨ (p5 ∧ p2)) ∨ (False → (False ∧ (True ∨ p4)))) := by
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
theorem thm_5_vars_791543074352235491856930734528 : (((True → (((((((((((p1 → p4) → p2) ∧ p1) ∨ (p5 ∧ (p2 ∧ p3))) ∨ p2) ∨ False) → True) ∨ p1) ∨ (False ∧ p1)) ∧ True) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179752868817607729863056325515 : (((((p2 → p4) ∨ ((p1 ∧ (p4 ∧ False)) ∧ p3)) → (p2 → p3)) ∧ p5) → ((((p4 ∧ (False ∨ p4)) ∨ (False ∨ (p2 ∨ p5))) → p2) ∨ p5)) := by
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
theorem thm_5_vars_68077319728351509727247681154 : ((p2 → (p3 ∨ ((((((p1 → (p1 → True)) → ((p2 ∨ p3) → (p3 ∨ False))) ∨ (p3 → p5)) → False) ∨ (p4 ∨ p2)) ∧ (False → p4)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114221601745329630798394165280 : ((((True ∧ p4) → (False → (p5 ∧ ((True → ((False ∨ ((p3 ∧ p3) ∨ (p5 → p4))) ∧ p1)) ∨ True)))) → ((p5 → p1) ∨ True)) ∨ (p2 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166336395704557416310417473809 : ((p5 ∧ (p3 ∨ (((p5 → p3) ∧ ((((False ∨ True) ∨ True) ∨ (p5 → p4)) ∨ p3)) ∨ p3))) ∨ ((p1 ∨ (p3 ∨ True)) ∨ (p2 → (True ∧ p3)))) := by
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
theorem thm_5_vars_113581328394859746681248874849 : (((p1 ∧ ((True ∧ p5) ∧ ((p3 ∧ (True ∨ ((p2 → p4) ∧ (True ∧ (p1 ∨ (True ∨ (True → p2))))))) ∧ p4))) ∨ (False ∨ False)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111163710394606992280298419606 : ((((((True → p5) ∧ p5) → p2) ∧ (p2 → (((p5 → (p3 ∧ p3)) ∧ ((False ∧ (p3 ∧ (False → p1))) ∨ True)) ∧ p2))) ∧ p1) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88222327151263495212266474628 : (((p4 ∧ (True ∧ (p4 → False))) ∧ ((p2 ∧ p4) ∨ ((p2 → p1) ∨ ((((p3 ∧ p5) ∨ p5) ∧ ((False → p4) → (p3 → p3))) ∨ p3)))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h11 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h12 := h7 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h15 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h16 := h7 h15
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h21.left
          let h23 := h21.right
          -- One of the premise coincides with the conclusion.
          exact h23
        case inr h24 =>
          -- One of the premise coincides with the conclusion.
          exact h24
      case inr h25 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h26 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h27 := h7 h26
        -- False on the left can always be used.
        apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135345076550194787498303724008 : (((True ∧ (p1 ∨ ((((p4 → (False ∨ p2)) ∧ ((p2 → (p3 ∧ True)) ∨ False)) ∨ p5) ∧ False))) ∧ (p1 ∧ (False ∨ p1))) ∨ (True ∨ (p1 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117647937664647342605176303957 : ((p3 ∧ ((False → (True ∧ ((p1 → ((p2 → ((p5 ∨ p4) → p3)) ∧ ((True ∨ p1) → p1))) ∨ (False ∧ (p3 ∨ p1))))) → False)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786570213517438955027394077631 : (((p4 ∨ ((((p1 ∧ p4) → ((p1 → p2) ∨ p5)) ∨ (p5 ∧ p3)) → ((p4 → (((p3 ∨ p3) ∧ p1) ∧ (False ∧ False))) ∨ (False ∨ True)))) ∨ p2) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47426853649119891746673563868 : (((p1 ∧ (p5 ∨ ((p1 → ((p2 → (p3 ∧ ((p5 → (p4 ∨ p1)) ∧ False))) → ((p1 → (False ∨ p1)) ∨ True))) → p5))) ∨ (p5 → p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760665422764224858819545901644 : (((p2 ∧ (p5 ∧ (p1 ∧ ((p1 ∧ (p2 → ((p4 ∨ (p5 ∧ True)) ∨ (True → ((True ∧ (p2 ∨ ((p1 ∨ p3) ∨ p5))) → True))))) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704964452913884374094652883870 : ((((True → (((False ∧ p1) ∧ False) ∧ ((p1 → True) → p1))) → ((((((p3 ∨ p4) ∨ p3) ∨ p2) ∨ p4) ∨ (p4 → p4)) ∧ (p5 ∧ p2))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h10
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151183075648157675230027154397 : ((((((p4 ∧ (p5 ∨ (p5 → p1))) ∧ p4) ∨ (p5 ∧ p1)) → (((p3 ∨ False) ∧ p3) ∨ (p5 ∧ p4))) → False) → (p1 ∨ ((True ∧ False) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_137066806854956725773672326499 : (((p3 → p4) → ((((p2 → True) → (p1 → ((((p1 ∨ p3) → (False → p3)) ∨ (p4 → True)) → False))) ∧ p4) → p2)) ∨ (True ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55295106271749876463376719484 : (((p3 ∧ ((p1 → p3) ∧ (p4 ∧ False))) ∨ ((p5 ∨ (p1 ∧ ((p5 ∧ False) ∧ (p2 ∧ p1)))) → ((p4 → False) ∧ ((p4 ∨ False) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68614579572626323492189371659 : ((p4 → (((p3 ∧ ((p3 ∧ ((p3 → (False ∧ p4)) ∨ p5)) ∧ (p3 → (p4 ∨ p3)))) → ((((p5 → p3) ∧ False) ∨ p4) ∧ p5)) ∨ p5)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h13.left
  let h16 := h13.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h17 =>
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h18 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h19 := h17 h18
    -- We need to get the left conjuct of h19 based on <expert-advice>.
    let h20 := h19.left
    -- False on the left can always be used.
    apply False.elim h20
  case inr h21 =>
    -- One of the premise coincides with the conclusion.
    exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68114905389822669188634283529 : ((p2 → (p2 → (p3 → (p1 → ((False ∨ p4) → (((((False ∨ p2) ∨ False) ∧ p4) ∨ ((p3 ∧ p1) ∨ p3)) → ((False ∧ p5) ∨ p2))))))) ∨ p5) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h20 =>
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h23 =>
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46161088355008496805589990077 : ((((((((True → (((p3 → p5) ∧ (p2 ∧ True)) → p3)) → False) → p2) → p1) → ((p2 → p3) ∨ (p2 → False))) → p3) ∧ (p3 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668561224601568853948996788017 : ((((((p2 ∨ (p4 ∨ p4)) ∨ (((((p4 → (p3 ∧ p2)) ∧ (True ∨ (p4 ∨ False))) ∧ False) ∨ True) ∨ p5)) ∧ False) ∨ (False ∨ (p2 ∨ True))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_39521824281292711110513111449 : (((False ∨ ((p5 ∧ ((((((p3 → (p1 → p2)) ∨ True) → p2) ∨ ((p1 ∨ p4) → p3)) ∨ True) ∧ (p2 ∨ False))) ∧ (p5 ∨ p5))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962427566143730004896381389943 : ((((True → False) ∧ (False → (True ∧ (((False ∧ p5) ∧ p4) ∨ ((p5 ∨ p5) ∧ (((False → (p4 ∧ p1)) ∨ (p5 ∧ (p4 ∨ True))) ∧ p4)))))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117762903007349327463111568024 : ((p4 ∧ (((True ∨ False) ∧ ((((p2 ∨ ((False ∧ ((p1 → p1) → p5)) → (p5 → (True ∧ p1)))) ∨ p1) → p4) → p2)) → False)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50337267658034838345383876572 : (((((((p4 → p2) ∨ p3) → p4) ∧ p3) ∧ ((True ∧ (((True ∧ p2) ∧ (p2 ∨ p2)) ∧ True)) ∨ True)) ∨ ((p1 → False) ∨ (p1 → True))) ∨ p4) := by
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
theorem thm_5_vars_729257334265223257363090699765 : (((((p5 → p4) ∧ True) → (((((p3 → p1) ∧ p1) ∨ ((p4 ∨ ((p3 → (True ∧ p5)) ∧ False)) ∨ (True ∨ True))) → (p5 → p1)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622383938944697758098223514624 : ((((p3 ∧ ((p1 ∨ ((True ∧ (p2 → p3)) ∨ ((p4 ∨ p4) → (p1 ∧ (p2 ∨ False))))) ∧ ((True ∧ (p2 → (p5 ∧ p3))) → p5))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157983204790049865421651052833 : (((((p4 ∨ (p2 ∨ False)) ∨ (p4 ∨ p5)) ∨ True) → ((p2 ∧ (p1 → ((p3 → p1) → p1))) ∧ p4)) ∨ (p2 → (((True ∧ False) → p2) ∨ p4))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207683751401530100662447335470 : ((((p5 ∧ False) → (p1 → p2)) → False) → (p3 ∨ ((p4 ∧ True) ∨ ((p4 ∧ (p5 ∧ (((True ∨ (p4 → p2)) ∨ (True ∨ p1)) ∨ p2))) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ False) → (p1 → p2)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68491398560772114538033914344 : ((p3 → (p1 ∨ ((p4 ∧ ((True ∧ ((((p3 → ((p3 ∨ p4) → p2)) ∧ p3) ∧ p5) → (p4 ∧ (p2 → p3)))) ∨ p5)) ∨ (p2 → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118381313793689531064121122313 : ((p2 ∨ ((((p2 ∨ p5) ∨ ((False → p3) → p2)) → ((True ∧ p2) ∧ p4)) → ((p3 → (((p4 ∨ p5) ∧ p2) → p2)) ∧ p1))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225359700943298477718304835819 : (((p1 ∨ p5) ∧ False) ∨ (((((False ∧ (p3 ∨ p2)) ∨ ((p5 ∧ p5) → ((p5 ∨ p2) ∧ ((True ∨ p5) ∨ False)))) ∨ p5) ∧ p2) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341736870175900769619331401633 : (p2 → (((False ∨ p1) ∨ ((p3 → (((False ∧ p5) ∧ (p1 ∧ p4)) ∧ ((p1 → (p3 ∨ p1)) ∧ p1))) ∨ (True ∨ (True ∧ False)))) ∨ (True → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_57915769856534277397020460506 : (((p5 ∨ (True ∨ True)) → (p4 → (((p1 ∨ True) ∧ ((p3 ∨ ((p1 ∧ (False → (p4 → (False ∨ p3)))) ∧ p2)) ∧ False)) ∧ (p5 ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162865744184658084250197170616 : (((((p3 ∧ (p4 ∨ (False ∧ False))) ∨ p5) ∨ ((p2 → (False ∧ p2)) ∨ p1)) ∨ (True ∨ True)) ∧ ((p5 ∨ p5) ∨ (False → ((p2 ∨ p2) ∨ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342930475383049802829059828173 : (p2 → (((p3 → (False → p1)) ∨ p1) ∧ ((True ∧ (p4 ∨ (p4 ∨ (True → (True ∨ p1))))) → (p3 ∨ ((p4 → p5) ∨ (p3 ∨ (False → p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721622788480792358182698624431 : ((((p5 ∧ (p2 ∨ (p5 ∨ False))) → (p1 ∨ (p4 ∧ ((p5 ∨ p2) ∧ (True ∧ ((False ∨ ((((p4 ∨ False) ∧ p3) ∨ p4) ∧ True)) ∧ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305511733540107121307632017457 : (p1 ∨ ((p1 ∨ (((p2 ∧ ((p5 ∧ p3) → False)) ∧ True) ∨ (p3 ∧ (p4 ∨ p4)))) ∨ (p1 ∨ ((p3 ∨ True) ∧ (((p1 ∧ p5) ∨ True) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197936198796583709096949796020 : (((True ∧ p1) ∧ (p2 ∨ (False ∨ (False ∨ False)))) ∨ (((p5 ∨ p3) ∨ p2) ∨ (((((((p4 → True) → True) → False) ∨ p4) → True) ∨ False) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115525152302946096742196698089 : ((((False ∨ p3) → (p4 ∨ ((p5 ∨ p4) ∧ p5))) → (p1 → (((p4 → p1) ∧ ((p2 → (False ∨ p5)) → (p4 ∨ p2))) ∧ p2))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111004644904261413414569251155 : ((((p2 → (p5 → ((((False ∨ (p1 → (p4 → ((p2 ∨ p3) ∧ False)))) ∧ p3) ∨ True) ∨ False))) ∧ ((p1 ∧ p5) → p2)) ∧ p4) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80053316555495408972405327635 : ((((p1 ∨ (p4 ∨ (((((False ∨ p3) → False) → p2) → ((((False ∧ p4) ∧ p1) ∧ p3) ∨ (p5 → p5))) ∨ p5))) ∧ True) → (False ∧ p4)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ (p4 ∨ (((((False ∨ p3) → False) → p2) → ((((False ∧ p4) ∧ p1) ∧ p3) ∨ (p5 → p5))) ∨ p5))) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45910726619424666579853343805 : (((p4 → ((True ∨ ((p2 ∧ p4) ∨ ((p2 ∨ ((p1 ∧ (False → p4)) ∨ p2)) ∧ (False → p4)))) ∧ ((True ∨ (p1 ∨ False)) ∨ p4))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111782122644800439408184731344 : ((((((((p3 ∧ p2) ∨ (p2 → (False → ((p1 → p2) ∧ False)))) ∨ p4) ∨ (p2 ∧ p5)) ∧ (p2 ∧ p5)) ∨ (True ∧ p5)) ∨ True) ∨ (False → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115794469080111501941773413265 : (((((p1 → p4) → p4) ∨ p4) ∧ ((p3 ∧ (((p5 ∨ p4) ∨ p1) ∨ (p2 ∨ (p2 ∨ True)))) → (p5 → (p1 ∧ (p3 ∧ p1))))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168651210463215819372822730932 : ((p4 ∧ ((p2 ∨ p3) ∧ ((p1 ∧ p3) ∧ (p3 ∨ (p3 → ((False ∧ (False ∧ p2)) → p4)))))) → (p2 ∨ ((False ∨ p2) ∨ ((True ∧ False) → p3)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h5.left
    let h15 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41628816885084975600734488962 : ((((((p1 → p5) ∨ p2) → (p1 → (True ∨ False))) → (((True → (p5 ∨ True)) ∨ p5) ∧ (p5 → (((False ∧ p5) ∧ True) ∨ False)))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190250311178670701542652787926 : ((((p1 ∧ (p4 ∨ ((False ∨ True) → p5))) ∧ p5) ∨ p4) ∨ ((p4 ∧ (p1 → ((p5 ∧ p5) ∧ True))) ∨ ((p2 → p1) ∨ (p3 → (p1 ∨ p3))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65619808603350895088285235369 : ((p4 ∨ ((p4 → ((p3 ∨ ((p5 ∧ (((True → (p3 ∧ p4)) ∧ True) ∧ True)) ∨ (p2 → (p3 → p2)))) → ((p3 → p4) → p2))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659988428477693456080133562634 : ((((((p3 → (p5 ∧ (((True → (p5 ∨ False)) ∧ ((p5 ∨ p4) ∧ p3)) → (p2 ∧ (p3 ∧ (p4 ∧ p3)))))) ∨ p1) ∨ p3) → (p5 → p5)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313359368701582594340144600386 : (p3 ∨ ((p3 → (((False ∧ p3) ∨ (((p5 ∧ (True → ((p3 → True) → ((p1 ∧ p4) → p4)))) ∧ ((p1 → p4) → p1)) ∧ p4)) ∨ True)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690124124270616287663075414687 : ((((False ∨ ((p3 ∨ p4) → (((False ∧ p2) → (p5 → False)) → (p4 ∧ (p1 → p3))))) ∨ (p5 → (((p5 → False) → p5) ∨ (True ∧ p1)))) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329507818344999211348534451071 : (True → ((True ∧ p1) ∨ (((((p4 → p4) → (p1 → p1)) → p2) ∧ (((p1 ∧ p4) ∨ False) ∨ p2)) → ((p4 ∧ ((p4 ∨ p2) → p5)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : ((p4 → p4) → (p1 → p1)) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h9
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254724250330352939928159747981 : ((p3 ∧ p3) → (((p1 ∨ p3) ∧ p3) ∧ ((True ∧ ((p2 ∨ p4) ∨ (p3 → ((((p4 ∨ (p2 ∧ (p1 ∧ p2))) → False) ∧ p3) ∨ p3)))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791534925031763876058688942013 : (((True → ((p5 → (p3 → (p5 ∧ ((p4 ∨ ((((p2 → p4) ∧ (p1 ∨ True)) ∨ ((p3 → (p2 ∧ p5)) → False)) ∧ True)) ∨ p2)))) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_809197312086614015918941966392 : (((p5 → (((p1 ∨ (((p2 ∨ False) ∧ (p1 ∧ p2)) ∧ (p1 → (((p3 ∨ p1) ∧ p2) ∧ (p4 ∧ (p2 ∧ p1)))))) ∧ (p2 → True)) ∨ p5)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_135483247368660003251810878442 : ((((p4 ∧ ((False ∧ p1) ∨ True)) → (((p3 ∧ (((True → True) ∧ p1) ∧ p2)) ∧ True) ∧ p3)) → (p3 ∨ (p1 → True))) ∨ ((p3 → p4) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139741198771237243315300172203 : (((p1 ∧ ((((False ∨ ((((p3 → ((p5 ∧ False) ∨ p3)) ∧ p1) ∧ (True ∧ p1)) ∧ p2)) → p5) → p2) → p5)) → True) → ((p2 → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652757972098818635882373662380 : ((((p2 ∨ ((((p2 → p5) ∧ p2) ∧ p1) → (((True ∧ (p5 → p4)) ∨ False) ∧ (False ∨ ((False → (p5 ∨ p2)) ∧ p4))))) ∧ (p5 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116718028713643497092123726047 : (((p2 ∧ p1) ∨ (p4 ∨ ((p5 ∨ ((True ∨ p1) → p1)) → ((True ∧ p3) → (((p3 ∨ p3) → ((True → p2) → p5)) ∨ p3))))) ∨ (True ∧ p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219406581099192804210084952712 : ((p3 ∨ (False → (False ∧ p2))) → ((p2 → (p2 ∧ p5)) ∨ (p1 ∨ ((((((p4 ∨ p2) → p1) → p2) ∨ (p3 ∨ (p1 → p1))) ∨ False) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111879622425112838522446672890 : (((((p4 ∧ (p1 ∧ (p3 → p2))) ∨ ((((p2 ∧ (p3 → p5)) ∧ p1) ∨ True) ∨ p4)) → (((p5 ∧ True) ∨ p1) ∧ p1)) ∨ p4) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_816968907953382788486839170249 : ((((((p3 ∧ False) ∨ ((p4 ∨ True) ∧ (((p1 → ((p1 → False) ∨ (((True → (False ∨ p2)) ∨ p2) ∨ True))) ∨ p2) → p5))) → False) ∧ p5) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 ∧ False) ∨ ((p4 ∨ True) ∧ (((p1 → ((p1 → False) ∨ (((True → (False ∨ p2)) ∨ p2) ∨ True))) ∨ p2) → p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46762554470155731348532924407 : (((p2 → (((False ∨ True) ∧ True) → ((p3 ∨ p4) → (p2 → (p1 → ((p3 → (True ∧ ((p1 ∧ False) ∧ True))) ∨ False)))))) ∧ (p1 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



