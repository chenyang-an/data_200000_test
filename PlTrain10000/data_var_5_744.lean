variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137927723672253619338821081988 : ((p4 ∨ (p5 ∧ (((True → p5) → p2) ∨ ((((((False → False) → False) ∧ (False ∨ p3)) → p3) ∨ (p1 → True)) → p4)))) ∨ ((True → p2) → p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51222696576229344372952357073 : (((((True ∨ (False ∧ p1)) ∨ (p1 ∧ p5)) → (p1 ∧ ((True ∨ p5) → ((False ∨ True) ∨ p5)))) ∨ ((((p3 → p4) → p1) ∨ p2) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65785374561136238646597230775 : ((p4 ∨ (((p3 ∧ (p1 ∧ (p4 ∨ (p1 ∨ ((False → p3) → False))))) ∨ p3) ∧ (False → (False ∨ ((False → (p1 ∨ p2)) → (p3 ∧ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185753974983553575156830045784 : ((p3 → (p2 → (((True ∨ False) ∧ (p4 ∨ p4)) ∨ (False ∧ p2)))) ∨ (p2 → ((p5 → (True ∧ p4)) → ((True ∧ (p5 → (p5 ∧ p4))) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157623819026603158586983434282 : ((((((False ∨ True) → (False ∧ False)) ∨ p1) ∧ (((p4 ∧ False) ∧ p3) → p2)) ∧ ((p4 ∨ p1) ∨ p1)) ∨ (True ∨ ((p3 ∨ p2) ∨ (p5 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663532790456128501454286031347 : ((((True ∧ (((False ∨ (p3 ∨ (p5 ∨ True))) ∧ ((p2 → (((False ∧ True) → (p5 ∧ p3)) → (p2 → p3))) → p2)) → p1)) → (p2 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727511932605714231895083226951 : ((((p4 ∧ (p4 ∧ p5)) ∨ ((True ∧ ((((True ∧ p5) → False) ∨ ((False ∨ p5) ∧ p3)) ∨ (p1 ∨ p1))) → (p2 → (False ∨ (False ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227756617134279319428082686675 : ((p1 ∧ (p4 ∨ p2)) ∨ (((p4 ∨ (p5 ∧ ((False → p3) ∨ ((False ∧ p2) ∧ (True → (p2 → p3)))))) ∨ (False → (p4 ∨ (p1 → p1)))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621111429761561418534105910862 : (((((p4 → True) → (p3 → ((p3 ∨ ((p2 ∨ p2) → p5)) ∧ ((((p4 ∨ p5) → (p5 → (p3 ∧ p4))) ∨ p5) ∨ (p2 ∨ p3))))) ∨ p3) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729552998854727879632914346646 : (((((p3 ∨ False) ∨ p2) → (((False → (p2 ∨ p3)) ∧ (((p2 ∧ False) ∨ p4) ∨ p3)) ∨ (p1 → (((p2 → p1) ∧ p5) ∧ (False ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615091369958140635877206227030 : ((((((((((p4 ∧ p3) → ((p3 → p3) ∨ (p1 ∨ True))) ∧ p3) ∧ p4) ∧ True) ∧ p1) ∧ (((p3 ∧ True) ∧ p3) ∧ (True → p4))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259737730807535818736213858537 : ((p1 → p2) → (((p2 ∨ p5) ∨ ((p2 → (((False ∨ (p5 ∧ (p3 ∨ p3))) ∧ p1) ∨ (((p5 ∨ p4) → p3) → (False → False)))) ∨ p1)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695396045273025942600332457145 : ((((((p1 ∨ (False ∨ False)) → (p3 → ((p3 ∨ False) → p2))) ∧ (False ∨ p1)) → (((p3 → ((p4 → p5) ∧ (False ∨ p1))) ∧ True) ∨ True)) ∨ p4) ∧ True) := by
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
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115615280215564558111937984793 : (((p5 ∨ (p2 ∧ (p3 ∨ (p1 ∨ False)))) ∧ ((p4 ∨ (((((False ∨ p3) ∧ ((p3 ∧ True) → p2)) ∨ False) ∨ p1) ∧ False)) ∧ p5)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50098053996800373771456322444 : (((p4 ∧ ((((p1 ∨ ((p2 ∧ True) ∨ True)) ∨ (False → ((p4 ∨ p1) ∨ (True → True)))) → p2) ∨ p1)) ∧ (p5 → ((p3 → p2) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329140650631201150270569224569 : (True → ((p3 → (p2 ∨ (p2 ∨ p2))) ∨ ((p2 ∧ ((p1 ∧ p2) ∧ ((((p5 ∧ (p1 → True)) ∨ True) → (p5 ∨ (p4 ∨ p4))) ∨ False))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245293619079130276850795918840 : ((p2 ∧ p2) ∨ (((p1 ∧ ((p4 ∨ p5) ∧ ((True ∧ p4) → ((True ∨ ((p4 ∨ p2) ∨ (p5 ∧ p4))) ∨ p1)))) → (p4 ∧ p3)) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185354373913403487232968776955 : ((p4 ∧ ((p1 ∨ p1) ∨ (p4 ∨ (((p5 ∨ p5) → p4) → p2)))) ∨ ((p5 ∧ (p5 ∧ ((p2 → (p5 ∧ p4)) → (p5 ∨ (p1 ∨ p4))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755461135524648025607170181117 : (((p1 ∧ (((p5 ∧ p5) ∨ (((p1 → (p3 ∨ ((((False → ((p4 ∧ p2) ∨ True)) → True) → (p4 ∨ True)) ∨ p2))) ∧ p5) ∧ True)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16600100195322114910018107577 : (((((((p3 ∨ ((p4 ∨ p2) ∨ p2)) ∧ (p3 → p4)) ∧ (((p1 ∧ p2) ∧ (p5 → False)) → p2)) ∧ p2) ∨ True) ∨ ((p5 ∧ True) ∧ True)) ∧ True) := by
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
theorem thm_5_vars_47158672485676389348645064094 : ((((p1 ∧ (((((p4 ∨ (p2 ∨ p3)) ∧ p1) → p2) → (p4 ∨ (p1 → True))) ∧ p1)) → (p3 ∨ (p4 → (p1 → p5)))) ∨ (False → False)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55960143717898386858304965993 : (((((True ∨ p5) ∧ False) ∧ True) ∨ (((p4 ∨ False) ∧ (True → True)) ∧ (((p5 ∨ (True → (False ∨ p5))) ∨ p1) ∧ (p2 → (p3 ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138221878661865272852604718547 : ((p2 → (((p3 ∨ p5) → (((True ∧ p2) → p5) ∨ (p2 ∧ ((p4 ∨ p2) → (p4 → (True → (True ∧ p1))))))) → p5)) ∨ ((p5 → True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786957341135211430566312534093 : (((p4 ∨ ((False ∧ p5) ∧ ((p2 ∧ p4) ∨ (((False ∨ p1) → (p1 ∨ (p3 ∨ (False ∧ p1)))) ∨ ((((p3 → p3) ∨ p3) ∧ p1) → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656948793764164481527463822950 : (((((((False ∨ p3) → p1) ∧ p4) → ((p3 ∧ ((p1 ∧ p1) → (p1 ∧ p3))) ∨ (False → (p1 ∨ (True ∨ (p2 ∨ False)))))) ∨ (False → p3)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18898971892989651907515240610 : ((((p5 ∨ p3) ∨ (((((p1 → (p2 ∧ True)) ∨ False) ∨ p3) ∧ (p1 ∧ p5)) ∧ (p2 ∧ p5))) ∨ ((p2 → ((p3 → p4) → True)) ∨ p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142395978763450225740125646139 : ((p4 ∧ ((False ∨ (((False → (False → p2)) ∧ p1) ∨ ((((p4 ∨ p1) ∨ p1) ∨ p2) ∨ p5))) ∧ (p5 ∨ (p4 → p1)))) → (p4 → (p1 ∨ True))) := by
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
  cases h5
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- Disjunctions on the left can always be decomposed.
            cases h17
            case inl h18 =>
              -- Disjunctions on the left can always be decomposed.
              cases h6
              case inl h19 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h20 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
            case inr h21 =>
              -- Disjunctions on the left can always be decomposed.
              cases h6
              case inl h22 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h21
              case inr h23 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h21
          case inr h24 =>
            -- Disjunctions on the left can always be decomposed.
            cases h6
            case inl h25 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h24
            case inr h26 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h24
        case inr h27 =>
          -- Disjunctions on the left can always be decomposed.
          cases h6
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
        cases h6
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133884692443562625287449224477 : (((p5 ∧ (p1 ∨ (False ∧ ((p4 ∧ (p5 → (False → ((p1 ∧ ((p4 ∧ (False → True)) → p4)) ∧ p3)))) ∨ p5)))) ∧ p3) ∨ (p4 ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646387104033621423945362943178 : ((((False → (p3 → ((((False ∧ (False → ((p4 ∨ False) ∧ (p2 ∧ ((p2 ∧ (True → True)) ∧ (p4 → False)))))) → p5) ∧ p4) ∧ p1))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46809634103085505276437236670 : ((((((((p4 → (True ∨ p4)) → p1) ∧ (p1 ∨ (p1 ∧ ((True → p4) ∨ (p5 → p5))))) → (False ∧ p2)) ∨ p1) ∧ True) ∨ (True ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68381052515060369623259471751 : ((p3 → ((True ∧ (p5 → (False ∧ p2))) ∨ ((p5 ∨ ((p1 ∧ (True ∧ (True ∧ p4))) ∧ (((p1 ∧ (p5 ∧ True)) ∨ p4) ∨ p5))) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301996123498741328956369666907 : (False ∨ ((p4 → p3) → (((p5 ∧ (((p4 ∧ p2) ∨ False) ∧ p5)) → p4) → (((p5 ∧ ((p5 ∨ p2) → False)) ∧ p3) → ((False → p3) → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : (p5 ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354693367485845765067869972373 : (p5 → (((((False → False) → p1) ∧ ((((True → p5) ∧ (((p4 → (True ∨ p2)) ∧ p2) → (True → p2))) ∨ False) → p3)) ∨ (True → True)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767903443064672180401779507017 : (((p5 ∧ ((((p4 → False) → p2) → (p5 ∨ (p1 ∧ (((p5 ∧ p4) ∧ p5) ∧ (p2 ∨ (False → (((p1 → p3) ∨ False) → p5))))))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790298353114898360747544734197 : (((p5 ∨ (p2 ∧ ((p5 ∧ ((p3 → p3) → p1)) ∨ ((True ∨ ((p4 ∨ (p1 → p5)) ∨ p4)) ∧ ((p5 ∧ p3) → (False ∨ (p4 ∨ p2))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728218807996590729112698413590 : ((((True → (p1 ∨ p1)) ∨ ((((False → p5) ∨ ((True → (p3 ∧ False)) → ((False → p4) ∧ p5))) → (p4 ∨ (p5 → p5))) ∨ (p3 → p2))) ∨ p2) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52875635799583195295848406324 : (((p5 ∧ (((((p4 ∨ p4) ∨ p4) ∨ p5) ∧ p4) ∧ ((p3 ∧ p2) ∨ False))) → ((True → False) ∨ ((p2 ∧ (p1 ∨ (p4 ∨ p3))) ∨ True))) ∨ p5) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- False on the left can always be used.
          apply False.elim h14
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h19 =>
          -- False on the left can always be used.
          apply False.elim h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h24 =>
        -- False on the left can always be used.
        apply False.elim h24
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h29 =>
      -- False on the left can always be used.
      apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158380992563358488923222653598 : (((False → True) ∧ ((p4 → p3) → (p1 → ((p5 → p1) ∧ (False ∨ ((False ∨ False) ∨ (p2 ∨ False))))))) ∨ (((p5 → (p5 → p5)) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115068220701898300675219070014 : (((((p3 ∧ p1) ∧ p2) ∨ ((True ∨ True) → (p3 ∨ (p3 → p5)))) ∨ (True ∨ ((p4 ∧ (p3 → False)) ∧ ((p1 → p4) → p2)))) ∨ (True ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147699326141139456016890630505 : (((((((p2 → ((True → p1) → p1)) ∨ (True ∧ False)) ∧ p1) ∧ False) → ((True ∨ (p5 ∧ p5)) ∨ p4)) → p2) ∨ (p3 → (p4 → (p4 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_927621854033565250724650825360 : (((((((p4 ∨ p4) ∧ p2) → (p5 → (p1 → p4))) → False) ∧ (False ∨ (((False ∧ False) ∧ False) ∨ (p1 → ((False ∨ False) → (p2 ∧ p5)))))) → p2) ∧ True) := by
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
      let h9 := h7.left
      let h10 := h7.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h11 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : (((p4 ∨ p4) ∧ p2) → (p5 → (p1 → p4))) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- Implications on the right can always be decomposed.
        intro h14
        -- Implications on the right can always be decomposed.
        intro h15
        -- Conjunctions on the left can always be decomposed.
        let h16 := h13.left
        let h17 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h18 =>
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h19 =>
          -- One of the premise coincides with the conclusion.
          exact h19
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h20 := h2 h12
      -- False on the left can always be used.
      apply False.elim h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167985150671233750840220204531 : (((((p5 ∧ p2) ∧ p1) → (True → p4)) ∧ (p1 → ((p1 ∨ (p1 → (p4 ∧ p5))) ∨ p1))) → ((p3 ∧ (p3 → p1)) → ((p4 ∨ p4) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60716818483770020092307604755 : ((True ∧ (((p2 → p5) ∨ ((True ∨ False) → p3)) ∨ (((p1 → False) ∧ (p4 ∧ (p2 → (p5 → (p4 ∧ p3))))) → ((p5 ∨ p2) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193172894768574910382934309817 : (((((p4 ∨ p2) ∧ p5) ∨ p5) → ((p5 ∧ p1) ∨ p4)) → (p2 ∨ (((False ∨ p1) ∨ (True → (((p5 ∧ False) ∨ p2) ∨ True))) ∨ (False → p2)))) := by
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
theorem thm_5_vars_55001417535728789718196936423 : ((((True ∧ p1) → (p2 ∧ (True → p3))) ∧ (((p2 → False) → ((p5 ∨ True) ∨ p1)) → (((True → (p2 → p5)) ∨ True) ∨ (p2 ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751593892781675830703513898040 : (((True ∧ (p2 ∧ ((p4 ∨ (((p1 → p1) → ((p1 → (p2 ∧ (True ∧ (p3 ∧ ((p3 → p4) ∨ p4))))) ∧ p3)) → (p3 ∧ p3))) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317945026385616849959235290873 : (p4 ∨ ((p3 ∨ (((p4 ∧ (p5 → ((False ∧ (p3 → p5)) ∨ p3))) → p2) → ((p3 ∨ True) → ((p5 ∧ p1) ∨ (p4 → (p1 ∨ True)))))) ∨ False)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349578052522065345078715562052 : (p4 → (((False ∧ (((p2 → (p5 ∨ p1)) ∨ p2) ∨ (p2 ∧ (p3 ∧ ((((p3 ∧ p1) ∨ p4) ∨ p4) ∧ ((p5 → p5) ∧ False)))))) ∨ p4) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254285961654916117290494681453 : ((p2 ∧ p3) → ((p4 → ((p5 → ((True → (p1 ∧ p2)) → (p1 ∧ p5))) → ((p2 ∨ p5) ∧ (p5 ∨ (p1 ∨ p1))))) ∨ (False → (p5 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113051863858431154857001893290 : (((p1 ∨ (p2 ∧ (p1 ∨ (p4 ∨ (p2 → ((((p3 ∨ p4) ∨ p3) ∨ (True ∧ True)) ∨ (p2 ∨ ((p5 ∨ p5) → p1)))))))) → False) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190565174889774139871506738452 : (((((p4 → p2) ∨ True) ∧ ((True ∨ p2) ∧ p5)) → p4) ∨ ((True ∨ p4) ∧ (((p1 ∧ p2) ∨ ((p4 → p4) ∧ p3)) ∨ ((p2 ∧ p1) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200365655613147591625374828793 : (((p2 → False) ∧ ((p2 ∨ (p5 ∧ p5)) → p4)) → (False ∨ (p5 ∨ ((p2 ∧ ((p2 ∨ (p5 ∨ ((p4 ∧ False) ∧ True))) → (p2 → True))) → False)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299165287382343047781416233576 : (False ∨ ((((((((p2 ∧ ((p4 ∧ p1) → p3)) ∨ p1) ∨ p1) ∨ p4) ∨ (False ∧ ((((p4 ∨ p3) → p3) ∧ p2) → p5))) ∨ p1) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53243038961784382370773063720 : (((((p1 ∧ p2) → p4) → (False ∧ (p5 ∨ (p3 → (p3 → p1))))) ∨ (p5 ∨ ((p3 ∧ (p2 → (p1 ∧ p4))) ∧ (False → (p3 → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168953059931903077239465256955 : ((True → (p1 → (((p1 ∨ (False ∨ (True → p1))) ∨ (False ∧ ((p1 → p5) ∧ p1))) ∨ p1))) → (((p5 → (p3 ∨ p5)) → (p5 ∧ p3)) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p5 → (p3 ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149286368852952480214479038106 : (((p3 → p1) ∨ ((p4 → p2) → (False ∨ (((((True ∧ p2) ∨ p2) ∧ p5) ∧ (p5 ∧ p5)) ∧ (p5 → p3))))) ∨ ((True ∧ p1) → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259033424766677286772601736742 : ((True → p4) → ((p3 ∧ (p4 ∧ ((p4 ∨ p5) → False))) ∨ ((p4 ∨ (p2 ∧ p1)) → ((True ∨ p3) ∨ (p1 → ((False ∨ p2) ∧ (p1 ∧ False))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586318857481641797284319853788 : ((((((((p2 ∧ (p2 ∨ False)) ∧ p1) ∧ True) ∧ (True ∨ (p1 → ((p1 ∧ (p2 → p3)) ∧ (((False ∧ True) → p4) ∧ p4))))) ∧ False) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111770532898161500843000422614 : ((((p2 ∧ (((False ∨ p5) ∨ p4) ∨ (((p3 → (p3 ∧ ((p4 ∧ (p5 ∧ p2)) → p5))) → p1) → False))) ∧ (False ∨ p1)) ∨ False) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148302565179689926610855308005 : ((((p3 ∧ (p1 ∨ p1)) ∨ (((p1 ∧ p2) → ((False → p2) ∧ (True ∧ p5))) ∨ p3)) → (p5 → (p2 → p4))) ∨ ((True → True) ∨ (p1 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51389212668235740558445867039 : ((((True ∧ ((((p3 → (p5 → ((p3 ∧ False) → (p1 ∨ p1)))) ∧ False) ∧ p1) → False)) ∨ True) → ((p5 ∧ p4) ∨ ((p3 ∨ p2) ∨ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154339192400095821570553912993 : (((p5 ∨ ((((((False → (p3 ∧ True)) ∧ p1) ∨ (p5 ∨ p3)) → True) → (p1 ∨ False)) ∨ False)) ∨ True) ∧ (p2 → ((p5 ∨ p3) → (True ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208348093601827192480456945947 : (((p5 → False) ∧ ((p3 → p5) ∨ False)) → (p1 ∨ (p5 ∨ ((False → (p2 ∨ ((p5 ∧ p5) ∨ p2))) ∧ ((p1 ∧ (p5 ∧ p4)) ∨ (p3 → p4)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113314672231056415571832020760 : ((((False ∨ (p1 ∧ False)) ∧ (True ∨ (p5 ∨ (True ∧ (p1 ∧ (p5 ∨ (p2 ∧ (False → (p5 ∨ (True → p5)))))))))) ∧ (p4 → p2)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591949663131017954106809020696 : (((((((p3 ∧ p1) → True) → ((p4 → True) ∧ (p2 ∧ (p4 ∧ (((((True ∧ p1) ∨ p1) → p3) ∧ p1) → True))))) ∨ (p5 → False)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342526859247030044040560515711 : (p2 → ((p3 ∨ (((p3 → p5) ∧ ((True ∨ ((p3 ∨ p2) ∧ p5)) ∧ p2)) ∨ p4)) → ((p1 ∨ True) ∨ (p1 ∧ ((p5 → p5) ∨ (p3 ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h14 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h15 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46540160489502644262601868824 : ((((True → p5) ∨ ((((((p5 ∧ True) ∧ (p3 → p3)) → (p3 ∧ (p5 ∨ (p5 ∨ p5)))) → p4) → (p5 ∨ True)) ∧ p1)) ∧ (True → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649106964596429412725340055073 : (((((((((p3 ∨ ((True ∧ False) ∨ (True ∨ p2))) → False) → True) ∨ False) → (p4 ∨ ((p2 ∨ (p1 → p4)) → False))) → p4) ∧ (p1 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68628995018895269663274311916 : ((p4 → ((False ∨ ((((p1 ∧ p2) ∨ ((p4 → (((p3 ∧ p1) ∨ p4) ∧ ((p2 ∧ p2) ∧ (False ∨ p1)))) ∨ p5)) ∨ p5) ∨ p4)) ∨ p1)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329134729248542956353710442816 : (True → ((p4 ∨ ((p4 ∨ True) ∧ p4)) ∨ ((False ∨ ((True ∧ (True → p4)) ∨ (((True → (p4 ∨ (p1 ∧ p4))) → p4) ∧ p4))) → (p3 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43492326012763627133048366746 : ((((p4 ∧ ((False → p2) → (False ∨ (p1 ∨ (((p5 → False) ∧ (p3 ∧ (False ∧ ((p4 → p4) ∨ False)))) → (True → False)))))) ∨ True) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156884232235614798868708193680 : (((((((p4 ∧ (False ∧ (p2 ∧ p1))) ∨ ((p1 → p3) ∨ p2)) → (False ∨ False)) → p5) ∨ p1) ∨ p4) ∨ ((False ∧ ((p1 ∨ False) ∧ p1)) → p2)) := by
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
theorem thm_5_vars_111907004827267492251327547533 : (((((((p5 ∧ p1) ∨ (True → False)) ∨ ((p2 ∧ p4) ∧ p3)) ∨ p1) ∧ ((p3 → (p2 ∧ ((p2 ∧ False) ∧ False))) → p2)) ∨ p3) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152117969626084195903326548100 : ((((False ∨ ((p5 → (False → p5)) ∨ p2)) → p2) ∧ (False ∨ ((p2 → ((p5 ∧ True) ∧ (False ∧ p1))) → p3))) → (((True → True) → True) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (False ∨ ((p5 → (False → p5)) ∨ p2)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h7
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55795553635036869017112066136 : ((((p4 ∨ True) ∨ (True → p2)) ∧ (((((p4 ∨ (p2 ∨ p4)) ∨ (p3 ∧ (False → (((p3 ∨ p2) → p5) → False)))) → p4) → p2) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255535602621125432974443148184 : ((p5 ∧ p2) → (p3 → (((p5 → (((p1 ∨ ((((p3 ∨ (p2 ∨ (True → p5))) ∨ p3) → (p1 ∨ p1)) ∨ p1)) ∧ p3) ∨ p2)) ∧ p4) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148886650597652402284506743784 : ((((p3 ∨ p3) ∧ (p1 → p3)) ∨ (((((p5 ∧ p5) → p1) ∨ (((True ∨ p5) ∨ p4) ∧ p4)) ∨ p3) ∧ False)) ∨ (False → (p5 → (p5 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60667448582236497402309327175 : ((True ∧ (((p4 ∨ (p5 → (p1 ∨ (p2 ∨ ((p2 ∧ (False → p5)) → (True ∧ p3)))))) ∨ p2) ∨ (p5 → ((True → (p2 ∧ False)) → False)))) ∨ False) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134502323832704380425789047117 : ((((((False → ((p1 ∧ False) ∨ p4)) ∧ False) ∨ (p1 → (p3 ∨ (p2 → (p1 → ((p5 → p2) ∨ p5)))))) ∨ False) → p1) ∨ ((p5 → p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62251770985732214079902650046 : ((p3 ∧ ((p5 ∧ (p2 → ((((True → p3) ∧ False) ∨ ((p3 ∧ (False → p5)) ∨ (p4 ∨ p5))) → (p3 ∧ (False → (True → p4)))))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197453219492856771203637373933 : ((((False → (p2 → p3)) ∨ p3) ∧ (p2 ∨ p3)) ∨ (p1 → ((((p1 → ((p4 → p2) → p4)) → (False ∨ (p3 ∧ False))) ∧ p1) ∨ (False → p2)))) := by
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
theorem thm_5_vars_184046047036650882428025972103 : ((((((p3 ∨ p3) ∨ (p2 ∧ p5)) ∨ p4) ∧ (False ∨ p4)) ∨ True) ∨ (((p1 → p5) ∨ p5) → (p5 ∧ ((p2 → ((True → False) ∧ p1)) ∨ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190095698297867934018244635059 : (((((p1 → p5) → (False ∧ p4)) ∨ (p5 ∨ p5)) ∧ p4) ∨ ((((True ∨ ((p1 ∧ False) ∨ (p3 ∧ ((p1 ∨ True) ∨ False)))) ∨ p5) ∧ False) → p4)) := by
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
      -- False on the left can always be used.
      apply False.elim h3
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- False on the left can always be used.
            apply False.elim h3
          case inr h15 =>
            -- False on the left can always be used.
            apply False.elim h3
        case inr h16 =>
          -- False on the left can always be used.
          apply False.elim h16
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173384493402700282261461296121 : ((p4 → ((((p2 ∧ ((p3 ∨ (p2 → p4)) ∨ p2)) ∨ p3) ∧ p1) ∨ (False ∨ True))) ∨ (p2 ∧ (((p5 ∧ p2) → p2) ∧ ((True ∨ False) ∧ True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256533033316084109575273939543 : ((False ∨ p5) → ((((p3 → p5) ∧ (((False ∨ False) ∨ (p5 ∨ ((True ∧ False) ∨ (p4 ∨ p4)))) ∧ (True ∨ p4))) ∧ True) → (False ∨ (p4 ∨ p5)))) := by
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
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h15 =>
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h16
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h18 =>
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h17
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h26 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h27 =>
              -- False on the left can always be used.
              apply False.elim h27
            case inr h28 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h25
          case inr h29 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h30 =>
              -- False on the left can always be used.
              apply False.elim h30
            case inr h31 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h29
        case inr h32 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h33 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h34 =>
              -- False on the left can always be used.
              apply False.elim h34
            case inr h35 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h32
          case inr h36 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h37 =>
              -- False on the left can always be used.
              apply False.elim h37
            case inr h38 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245552995757409488201649573247 : ((p3 ∧ True) ∨ (((p5 ∧ p2) ∧ (p3 ∧ p3)) ∨ ((p5 → ((False ∨ p5) ∨ (True ∨ (p2 ∧ True)))) ∨ ((((False ∨ p4) ∧ p4) ∨ p4) → p3)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49652947371509883997246395458 : (((((p4 → p2) ∧ p1) ∧ (((p5 → ((p4 ∨ True) ∧ p1)) ∨ (p1 ∨ (p5 ∧ p5))) ∧ (p1 ∧ (p2 → False)))) → (p4 ∧ (p2 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135779110609512344978303742078 : ((((p4 ∧ ((((p5 → p2) ∧ p5) ∨ p4) ∨ ((p2 ∨ p5) ∨ p1))) → False) → (((p3 → (p4 → p2)) ∧ p5) ∧ p3)) ∨ (False ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32012295100526618358810091427 : ((p1 ∨ (((p5 → False) → (p4 → ((((((((p1 → p4) ∧ p4) → False) → (p5 ∧ True)) → p1) ∨ (p4 ∧ p2)) → p2) ∨ True))) ∨ p1)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149975217124706052253221256351 : ((p4 ∨ (((((p1 ∨ p3) → (True ∧ p4)) ∧ False) ∧ True) ∨ (p2 → ((True ∧ (p5 ∨ (p3 ∨ p4))) ∧ p4)))) ∨ (p1 → (True ∨ (True ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746387708607309533739975389116 : ((((p2 ∨ p1) → ((((p3 ∨ (((p3 ∨ (p3 ∧ p1)) ∧ p3) ∨ ((p5 → True) → p3))) → p4) → p5) ∨ (False → (p3 → (p5 ∧ p4))))) ∨ p3) ∧ True) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h6
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130638029407617408797710533335 : ((((((False ∧ p2) ∨ p5) ∧ p3) ∧ ((p3 ∨ (((p4 ∨ p1) → p1) ∨ False)) ∨ p1)) ∨ (True → ((True → True) ∧ True))) ∧ ((p3 → p3) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150005775786784936304225535039 : ((p5 ∨ ((((p2 ∨ (p1 ∨ p1)) → True) → (p1 → (((p4 ∧ (p5 ∧ True)) ∨ p5) → (p2 ∨ p2)))) ∨ p5)) ∨ (((p2 ∧ p1) ∨ p2) → p2)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193454887574382849168578292181 : (((p5 → p1) ∧ (p3 ∧ (p4 ∨ (False ∧ (p4 → p4))))) → ((p1 ∨ p5) → ((p1 → (p1 ∧ ((((p4 ∧ p5) ∨ p3) ∨ p1) ∧ False))) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_886954653978843878172746132411 : (((((p5 → (((p3 ∧ p3) ∧ p2) ∨ ((p5 ∧ ((False ∧ ((p3 ∨ p1) → True)) ∧ p5)) → (False ∧ (p5 ∨ False))))) ∨ p1) → (p2 ∧ p1)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 → (((p3 ∧ p3) ∧ p2) ∨ ((p5 ∧ ((False ∧ ((p3 ∨ p1) → True)) ∧ p5)) → (False ∧ (p5 ∨ False))))) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
    -- Conjunctions on the left can always be decomposed.
    let h11 := h4.left
    let h12 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- False on the left can always be used.
    apply False.elim h15
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h17 := h1 h2
  -- We need to get the right conjuct of h17 based on <expert-advice>.
  let h18 := h17.right
  -- One of the premise coincides with the conclusion.
  exact h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60695570199442331623458152857 : ((True ∧ ((((True ∨ ((False ∧ (p5 ∨ p4)) → True)) ∧ p2) ∧ p3) ∨ ((p4 → ((p2 → True) ∧ (((False ∧ p2) ∨ p1) ∧ p4))) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707406846129761352662271976820 : (((((p1 ∨ (p5 ∨ (p5 → p1))) → (True → p4)) ∨ ((p2 ∨ (False ∨ (p2 ∧ ((p2 → p1) ∧ p1)))) ∨ (p1 ∨ ((False → p1) ∨ True)))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2697460286316532359672393101 : (((p5 ∨ (p3 ∨ True)) → (True → False)) → (((p2 ∨ (p5 ∨ ((p3 ∧ (False → True)) → p5))) ∧ (p2 ∨ ((p4 ∨ p4) ∨ True))) → p1)) := by
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
    cases h4
    case inl h6 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h7 : (p5 ∨ (p3 ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h8 := h1 h7
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h10 := h8 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h14 : (p5 ∨ (p3 ∨ True)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h15 := h1 h14
          -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
          have h16 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h15, we can now drive its conclusion.
          let h17 := h15 h16
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h19 : (p5 ∨ (p3 ∨ True)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h20 := h1 h19
          -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
          have h21 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h20, we can now drive its conclusion.
          let h22 := h20 h21
          -- False on the left can always be used.
          apply False.elim h22
      case inr h23 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h24 : (p5 ∨ (p3 ∨ True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h25 := h1 h24
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h26 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h27 := h25 h26
        -- False on the left can always be used.
        apply False.elim h27
  case inr h28 =>
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h30 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h31 : (p5 ∨ (p3 ∨ True)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h29
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h32 := h1 h31
        -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
        have h33 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h32, we can now drive its conclusion.
        let h34 := h32 h33
        -- False on the left can always be used.
        apply False.elim h34
      case inr h35 =>
        -- Disjunctions on the left can always be decomposed.
        cases h35
        case inl h36 =>
          -- Disjunctions on the left can always be decomposed.
          cases h36
          case inl h37 =>
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h38 : (p5 ∨ (p3 ∨ True)) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h29
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h39 := h1 h38
            -- We want to use the implication h39 based on <expert-advice>. So we show its premise.
            have h40 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h39, we can now drive its conclusion.
            let h41 := h39 h40
            -- False on the left can always be used.
            apply False.elim h41
          case inr h42 =>
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h43 : (p5 ∨ (p3 ∨ True)) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h29
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h44 := h1 h43
            -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
            have h45 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h44, we can now drive its conclusion.
            let h46 := h44 h45
            -- False on the left can always be used.
            apply False.elim h46
        case inr h47 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h48 : (p5 ∨ (p3 ∨ True)) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h29
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h49 := h1 h48
          -- We want to use the implication h49 based on <expert-advice>. So we show its premise.
          have h50 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h49, we can now drive its conclusion.
          let h51 := h49 h50
          -- False on the left can always be used.
          apply False.elim h51
    case inr h52 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h53 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h54 : (p5 ∨ (p3 ∨ True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h55 := h1 h54
        -- We want to use the implication h55 based on <expert-advice>. So we show its premise.
        have h56 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h55, we can now drive its conclusion.
        let h57 := h55 h56
        -- False on the left can always be used.
        apply False.elim h57
      case inr h58 =>
        -- Disjunctions on the left can always be decomposed.
        cases h58
        case inl h59 =>
          -- Disjunctions on the left can always be decomposed.
          cases h59
          case inl h60 =>
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h61 : (p5 ∨ (p3 ∨ True)) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h62 := h1 h61
            -- We want to use the implication h62 based on <expert-advice>. So we show its premise.
            have h63 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h62, we can now drive its conclusion.
            let h64 := h62 h63
            -- False on the left can always be used.
            apply False.elim h64
          case inr h65 =>
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h66 : (p5 ∨ (p3 ∨ True)) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h67 := h1 h66
            -- We want to use the implication h67 based on <expert-advice>. So we show its premise.
            have h68 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h67, we can now drive its conclusion.
            let h69 := h67 h68
            -- False on the left can always be used.
            apply False.elim h69
        case inr h70 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h71 : (p5 ∨ (p3 ∨ True)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h72 := h1 h71
          -- We want to use the implication h72 based on <expert-advice>. So we show its premise.
          have h73 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h72, we can now drive its conclusion.
          let h74 := h72 h73
          -- False on the left can always be used.
          apply False.elim h74



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172109510691062722080853558491 : (((p3 → (p3 → ((p4 → p1) ∧ (((True → p5) → p3) ∨ p1)))) → (True → p2)) ∨ ((True ∧ ((p4 → p3) → (False → True))) ∧ (True → True))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111455351942255585257148715665 : (((True → (True → (((True ∧ p2) → ((p5 → (p3 ∨ p2)) ∨ p5)) ∧ (p2 ∧ ((False ∧ (p5 ∨ p5)) ∨ (p3 ∧ p3)))))) ∧ False) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



