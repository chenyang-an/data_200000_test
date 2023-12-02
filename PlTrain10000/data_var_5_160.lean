variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737126870517905984986146153079 : ((((p3 → p4) ∧ (((p3 ∧ ((p5 ∨ p3) ∨ (p2 ∧ p5))) ∧ ((True → p3) ∧ ((((False ∧ False) → p3) ∨ p2) → (p2 ∧ p2)))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_551499387103489390919225712 : ((((p4 ∧ False) ∧ (False ∨ (((False ∧ (p4 ∨ (True ∧ p3))) ∧ ((True ∨ p4) ∧ p2)) ∧ (p3 ∨ ((p5 ∧ p3) → p4))))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158635548305973027650289964469 : ((p1 ∧ ((p2 → (False ∨ ((False ∧ (((p2 ∧ p1) ∧ p2) ∧ p3)) ∨ (False ∧ (p2 ∨ p1))))) ∨ p5)) ∨ (False ∨ (((True → p2) → p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164175816868260722575530273203 : ((p4 ∨ (p1 ∨ (p1 ∨ (((p4 ∧ False) ∨ (True → p4)) ∨ (p1 ∨ ((p2 ∧ p5) → p5)))))) ∧ (True ∨ (((p2 ∧ p5) → p3) → (False → p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774888309970505575784013095882 : (((False ∨ (((p2 ∨ (p4 ∨ p5)) ∧ True) → (p3 → (p2 ∨ ((p2 ∧ (((True → p2) ∨ (p2 ∨ p4)) ∧ (True ∧ (p3 → p3)))) ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769400519472054521751507765895 : (((p5 ∧ (False ∧ (p2 ∨ (True → (p4 ∧ (((p2 ∨ (False → ((((p1 ∨ False) → p1) ∨ p1) ∨ p4))) → (p2 ∨ True)) → (p1 ∨ p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735403294546072450731300212170 : ((((p4 ∨ p2) ∧ ((p1 ∨ (p2 ∨ (p3 ∨ (((p3 ∨ p5) → (p1 ∨ (p1 → (((p3 → p2) ∧ p5) ∧ p1)))) ∨ p1)))) → (p2 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200041821880753259904112450015 : (((False ∨ ((p4 ∧ p1) ∧ p1)) → (p4 → p2)) → (((p4 ∨ p2) ∧ (p2 ∧ p5)) ∨ ((p1 ∧ (p1 → ((p4 ∨ p3) ∨ p4))) → (p1 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256414976111681589700677901292 : ((False ∨ p3) → (((p4 ∨ ((((p1 ∧ True) ∧ p4) ∨ ((p4 → (p4 ∧ p5)) ∨ False)) → p1)) → False) ∨ ((((p2 ∧ p3) ∧ False) → p3) ∧ p3))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792825167553425429069640743204 : (((True → (((p1 ∨ p5) ∨ p2) ∨ ((((((p2 ∧ ((p3 ∧ p3) ∨ p3)) ∨ p2) ∨ p4) ∧ False) ∧ (True ∧ p2)) ∨ ((False ∨ False) → p1)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190901779220238855041166775406 : (((p3 ∨ ((p4 → (False ∧ p1)) ∧ p3)) → (p5 ∨ p2)) ∨ (((((False → p4) ∧ (True ∧ False)) → ((p4 ∧ (p3 ∧ True)) ∧ p5)) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116989353225399124075705924734 : (((True ∨ True) → (((p1 ∨ (((p5 → (((p1 ∨ (p3 ∨ (True → (p1 ∧ p4)))) ∨ p3) ∧ True)) ∧ p3) → p5)) → p3) → p1)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149085265751011137016132603323 : (((True ∧ (p4 → p3)) → (((False ∧ True) ∨ (((p4 ∧ (False ∧ p3)) → ((True ∧ p3) ∧ True)) ∧ p2)) ∨ False)) ∨ (True ∨ (p4 → (p1 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111514412516741147021450943185 : (((p5 → ((p4 ∨ ((p3 ∧ (((((p5 ∨ p3) ∧ p1) ∧ p1) → p1) → ((p4 ∧ (p5 ∨ p2)) ∧ p2))) ∧ p2)) → p1)) ∧ False) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4421248100304804231203207224 : (p1 → ((False → p3) ∧ ((((p1 ∧ (True ∧ p2)) ∨ ((p5 ∧ ((p2 ∨ p2) ∨ (True ∧ (p5 ∨ p2)))) ∨ (p4 ∧ p1))) ∧ True) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161811471953387616675838694878 : ((p5 ∨ ((p3 ∧ False) ∨ (p3 ∨ ((((False → False) ∧ p3) → p3) ∧ (p2 ∨ (p1 ∨ (p2 ∨ p4))))))) → (p5 ∨ ((p5 ∧ p1) → (p5 ∧ True)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- One of the premise coincides with the conclusion.
        exact h10
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- One of the premise coincides with the conclusion.
          exact h17
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h21
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Conjunctions on the left can always be decomposed.
            let h22 := h21.left
            let h23 := h21.right
            -- One of the premise coincides with the conclusion.
            exact h22
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h24 =>
            -- Disjunctions on the left can always be decomposed.
            cases h24
            case inl h25 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h26
              -- Conjunctions on the right can always be decomposed.
              apply And.intro
              -- Conjunctions on the left can always be decomposed.
              let h27 := h26.left
              let h28 := h26.right
              -- One of the premise coincides with the conclusion.
              exact h27
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h29 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h30
              -- Conjunctions on the right can always be decomposed.
              apply And.intro
              -- Conjunctions on the left can always be decomposed.
              let h31 := h30.left
              let h32 := h30.right
              -- One of the premise coincides with the conclusion.
              exact h31
              -- True on the right can always be proven directly.
              apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71377245141377742066693544244 : ((((True → False) ∧ (((p2 ∨ p1) ∧ p5) → ((p4 → (p3 ∨ p2)) ∧ (p3 ∨ (((p2 ∨ (True ∧ p2)) ∧ True) ∨ (True ∨ p2)))))) ∧ p3) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354263155776834185465317010424 : (p5 → ((((((p2 ∨ (((True ∨ True) ∨ p3) ∧ (p1 ∧ True))) ∧ (p4 ∨ p2)) ∧ (((p1 ∧ p5) ∧ p5) ∨ True)) ∨ False) ∨ (True ∨ p3)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_165154505672148893717694758520 : ((((p5 → ((True → p3) ∧ (p5 ∧ False))) ∨ ((p2 → p5) ∨ (p3 ∨ p1))) ∧ (True → p3)) ∨ (p2 → ((p4 ∨ ((False ∨ p5) ∨ p2)) ∧ p2))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67730458017981698341182243561 : ((p2 → ((((p4 → p2) ∨ p3) ∧ ((p1 ∨ p4) → (((p2 → p5) ∨ p5) ∨ (((((False ∨ p5) ∧ True) → False) ∧ p1) ∨ p5)))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257445693950234715261964903440 : ((p3 ∨ True) → ((((p1 ∧ p4) ∨ (((((p3 → False) → p1) ∨ p2) ∧ False) ∨ p1)) ∧ ((True → p2) → p3)) ∨ ((True ∨ p2) ∨ (p1 → p3)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56758899884375197634504274275 : ((((p4 → True) ∨ p4) ∧ (p4 ∨ ((p1 ∧ ((True → (((p3 ∧ p4) ∧ False) ∧ p2)) ∧ (True → (p1 ∨ p1)))) ∨ ((False ∧ False) → True)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66049738546009861568441357436 : ((p5 ∨ ((((p5 ∨ (p2 → ((False ∨ ((False → (p5 ∧ ((p3 → p3) → ((p5 ∨ False) → False)))) ∧ p4)) ∧ p4))) ∧ False) ∨ p1) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747764303191154118082522219197 : ((((False → p1) → (((p3 ∨ ((p1 ∨ ((((False → False) → p3) ∧ ((p5 ∧ True) ∧ p2)) ∨ p1)) ∧ p3)) ∧ p1) → (p3 → (p1 → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119351339035051863219674524923 : ((p3 → ((p2 ∧ p5) → (((p2 ∧ (p4 ∨ ((p4 ∧ (((p3 ∧ p3) ∧ True) ∧ p1)) ∨ p4))) ∨ (p1 ∨ p2)) ∧ (p1 ∨ p2)))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328281426489350273229611095422 : (True → (((p5 ∧ ((p3 → ((p1 → (p4 ∨ (p2 ∧ p4))) ∧ ((p1 ∧ p3) → p4))) → (True ∧ p2))) → p4) ∨ ((p3 ∧ p4) → (p4 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337525799084823137859115037996 : (p1 → ((((((p2 ∨ p4) ∨ (((p2 ∨ False) ∧ p5) ∨ (True ∨ True))) ∨ p1) → (p4 ∧ (p1 ∨ True))) → False) ∨ ((p4 → (p1 ∧ p4)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118208499353017123485756054202 : ((p1 ∨ (((((False ∨ (p2 ∧ ((p2 ∧ (p4 ∨ True)) ∧ p4))) ∨ (p4 ∧ ((p1 → p3) ∨ False))) ∨ (p1 ∧ p5)) → p2) ∧ True)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347261656009307723747714643457 : (p3 → (((True ∨ p2) → (((p5 ∧ p1) ∧ (p1 → False)) ∨ True)) ∧ (((p3 ∨ (p1 ∨ ((p5 ∧ p1) ∨ True))) → p3) ∨ (p4 ∧ (p4 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315798739846053329039020249916 : (p3 ∨ ((True ∨ p4) → ((p2 → p2) → ((False ∨ ((p3 ∧ (False ∧ (p5 → False))) ∨ ((False → p3) ∨ (p3 ∧ ((p3 ∧ p2) ∧ p3))))) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147223968009606722483830527713 : (((p5 → (((p3 → ((((p4 ∧ (p1 → (False ∨ (p4 → p4)))) → p1) ∧ p3) ∨ p2)) ∨ True) ∨ True)) ∧ True) ∨ ((p1 → (p1 ∧ p3)) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117045827385209259286829483439 : (((p4 ∨ False) → ((p3 ∨ (p1 ∨ (((p1 ∧ p5) → True) → (((p3 ∨ p1) ∧ p5) ∨ ((p2 → p5) → (p1 ∧ True)))))) ∧ p4)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125166247631549761327326549689 : ((((True ∨ p4) → False) ∨ (((p4 → False) ∧ (p4 ∧ p5)) ∧ (p1 ∨ ((p2 → (p4 → (((True ∧ False) ∧ p1) → p4))) ∨ False)))) → (False ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (True ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h12 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h13 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h14 := h8 h13
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h17 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h18 := h8 h17
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- False on the left can always be used.
        apply False.elim h19
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h20 =>
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h21 : (True ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h22 := h20 h21
    -- False on the left can always be used.
    apply False.elim h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h24.left
    let h27 := h24.right
    -- Conjunctions on the left can always be decomposed.
    let h28 := h27.left
    let h29 := h27.right
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h30 =>
      -- One of the premise coincides with the conclusion.
      exact h29
    case inr h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h32 =>
        -- One of the premise coincides with the conclusion.
        exact h29
      case inr h33 =>
        -- False on the left can always be used.
        apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158673310876120211709309006249 : ((p2 ∧ ((((p5 → False) ∧ ((True ∨ p1) ∧ (p3 ∨ (p4 ∧ (p2 → (True ∧ True)))))) ∧ p2) → p5)) ∨ ((p5 ∨ ((p3 ∨ p3) ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644990166080889973892762153814 : ((((p2 ∨ (p4 ∨ (p1 ∧ (p3 ∨ (((p2 ∨ (p1 ∨ p4)) → p1) → ((p3 ∨ p2) ∨ ((p4 → ((p3 ∨ p2) → p4)) → p2))))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346988022562552662153188505386 : (p3 → (((p5 ∧ False) ∨ (True → (p3 ∨ (p4 → ((True ∧ True) → (False ∧ (False → False))))))) ∧ (((p3 ∧ p2) ∧ ((p1 ∧ p3) ∧ p2)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40977458833085670947980214923 : (((((False ∨ p2) ∨ ((p1 ∧ (p5 ∨ True)) ∧ ((((p4 → (True → (p3 ∨ p2))) ∧ p2) ∨ (True → p2)) ∨ p1))) ∨ (p3 ∨ p2)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190601217932336102314682320704 : ((((p2 → p5) ∨ ((p4 ∨ p4) → (p2 ∧ p2))) → p3) ∨ ((p5 ∧ p2) → (((((p3 ∨ True) ∧ p2) ∧ p3) ∨ (False ∧ (p4 ∧ p2))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722779483675449803164480908661 : (((((p5 → p4) ∧ p4) ∧ (((((p5 → p3) ∧ (p2 ∨ p5)) → True) ∧ (((True ∧ ((True → p1) ∨ (True ∨ p5))) → True) ∧ p5)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183805060381006108932903582203 : ((((True ∧ ((p1 ∧ (True → (p1 → p2))) ∨ p5)) ∨ p2) ∧ p3) ∨ (((p5 ∨ (p2 → False)) → (p2 → (((p5 → False) ∧ False) ∧ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196684317450588925710280487894 : (((((p5 → (False ∨ p2)) ∨ p5) ∨ p3) ∧ False) ∨ (p3 → (False ∨ ((p1 ∨ p1) → (False → (((True ∧ (p5 ∧ (False → True))) ∨ p2) ∧ p3)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728629632375576206239450670100 : ((((p4 → (p1 → False)) ∨ (((((((True → (p5 → p4)) ∧ ((p5 ∧ p2) ∨ p2)) ∧ (p1 ∧ p4)) → (False → p4)) → p3) ∨ True) ∨ p2)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_205622470094128769946576566352 : (((p1 ∧ p3) ∨ (False ∧ (False → p5))) ∨ (p2 → ((p2 ∧ ((False ∨ (p2 → (p5 → ((p2 → p4) → (False ∨ p4))))) ∨ p4)) ∧ (p2 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328276113259853529216456031900 : (True → ((((p3 ∨ (p3 ∧ p4)) ∨ (((p1 → (((p3 ∨ (p2 ∧ p1)) ∧ p4) ∨ p4)) → True) → p1)) ∨ True) ∨ (p3 ∨ ((p1 ∨ p4) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630338976449262300162678531096 : (((((p1 ∧ (p2 → (p2 ∨ ((p1 → p4) ∧ (p4 → (((p2 → (p1 ∨ (p1 → (p4 ∨ p2)))) ∨ (True → True)) ∧ True)))))) ∨ p1) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47267233010898345024586270390 : (((((p3 ∨ (p2 ∨ p4)) ∨ p3) ∧ (((((((p4 ∧ p4) ∨ p1) ∨ p2) ∧ p2) ∧ (False → True)) → False) → (p2 ∧ p2))) ∨ (p1 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124082550358992927161204811122 : (((p1 → (((p4 → (p5 ∧ True)) → p2) ∨ ((p1 ∨ p4) ∨ True))) → (((((p5 ∨ False) ∨ p3) ∧ p1) ∨ p1) → (p3 ∧ p5))) → (p2 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672946781195422737821354186566 : ((((((p1 ∨ ((((p1 ∧ p1) ∨ p4) ∨ ((p1 → p2) ∨ True)) ∧ p1)) ∧ p3) ∧ (((p2 → p4) ∨ False) → p1)) → (p3 ∧ (p4 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263409731442100095974952481741 : (True ∧ (((p2 ∧ p2) ∧ ((((p5 → (((False → False) ∨ p2) ∧ p2)) ∨ p5) → (False ∨ (p4 ∧ p4))) → (p4 → p2))) ∨ ((p4 ∨ True) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119212559613733940531909495472 : ((p2 → ((((p5 → (p5 ∧ True)) → p4) → (p1 ∧ p2)) ∨ (((p4 ∧ (p3 → (p1 → p1))) ∨ (p3 ∧ p3)) ∧ (p1 ∨ p3)))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160362583430024105171767396042 : (((((False → p3) ∨ ((((p3 → True) ∧ p1) ∨ p3) ∨ (p3 → p4))) → False) ∧ ((True ∨ True) ∨ p2)) → (p3 ∧ (p5 ∨ (p5 ∧ (p1 ∧ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      have h6 : ((False → p3) ∨ ((((p3 → True) ∧ p1) ∨ p3) ∨ (p3 → p4))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- False on the left can always be used.
        apply False.elim h7
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h6
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : ((False → p3) ∨ ((((p3 → True) ∧ p1) ∨ p3) ∨ (p3 → p4))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- False on the left can always be used.
        apply False.elim h11
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h10
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : ((False → p3) ∨ ((((p3 → True) ∧ p1) ∨ p3) ∨ (p3 → p4))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h15
      -- False on the left can always be used.
      apply False.elim h15
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h16 := h2 h14
    -- False on the left can always be used.
    apply False.elim h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h21 : ((False → p3) ∨ ((((p3 → True) ∧ p1) ∨ p3) ∨ (p3 → p4))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h22
        -- False on the left can always be used.
        apply False.elim h22
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h23 := h17 h21
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h25 : ((False → p3) ∨ ((((p3 → True) ∧ p1) ∨ p3) ∨ (p3 → p4))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h26
        -- False on the left can always be used.
        apply False.elim h26
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h27 := h17 h25
      -- False on the left can always be used.
      apply False.elim h27
  case inr h28 =>
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h29 : ((False → p3) ∨ ((((p3 → True) ∧ p1) ∨ p3) ∨ (p3 → p4))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h30
      -- False on the left can always be used.
      apply False.elim h30
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h31 := h17 h29
    -- False on the left can always be used.
    apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134200652429215208202203769305 : (((((((p4 ∧ (False ∨ True)) ∨ (p1 ∨ True)) ∧ p5) ∨ p4) → (True → ((p1 ∨ (False ∨ False)) ∨ (p1 → p1)))) ∨ p2) ∨ ((p5 ∨ p2) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h17
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52564290709576747548674050560 : (((((True ∨ (p1 ∨ ((p1 ∨ (p3 ∨ p1)) → True))) → p5) ∧ (p5 ∧ p3)) ∨ ((((True ∧ p1) → (p3 → False)) ∧ (p5 ∨ p1)) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137979285672431558350623360040 : ((p5 ∨ ((p2 ∧ ((p5 ∨ p1) ∨ p5)) → (((p4 ∨ ((False ∨ p4) → (((p5 ∨ p1) ∧ True) ∧ p5))) → True) → p1))) ∨ (True ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617392961175254491223666503456 : (((((p1 ∧ ((p2 ∧ (p1 ∨ (p1 → p4))) → False)) → ((True ∨ False) → (((p3 ∧ ((True ∨ False) ∧ p5)) → p2) ∨ (p2 ∧ p3)))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322604457041191010071102840340 : (p5 ∨ ((p2 → (p4 → ((((True ∧ p5) ∨ (p2 → (False → True))) → (p3 ∨ (False ∨ (((p1 → p1) → (p4 ∨ True)) ∨ p2)))) → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157837981265810222069533405505 : (((((((p3 ∧ p1) → p1) → (p1 ∧ p1)) ∨ p2) ∧ True) ∧ ((p3 → p1) ∨ ((p1 ∨ p5) → p3))) ∨ ((p5 ∨ (False → (True ∧ p3))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_161483185142319929837129728433 : ((p3 ∧ (p4 ∨ (((False ∨ (p5 ∧ ((((p1 → p2) → (True → False)) ∨ p3) ∧ p1))) → p3) ∧ p5))) → (p2 ∨ (True ∧ (p3 ∨ (p5 → p4))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676663658789304408809565330373 : ((((p4 ∧ ((((p3 ∨ False) ∨ p2) ∨ True) → (((((p1 → p2) ∨ False) → (p1 ∧ False)) → p3) → p1))) ∧ (((p5 ∧ p3) ∨ p4) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338612590124746519705791131089 : (p1 → ((True ∨ (p2 ∨ p1)) → (p5 ∨ (p4 ∨ (p4 → (((((p3 → True) ∧ p4) ∨ True) ∧ ((p5 ∨ ((False ∧ False) ∧ True)) ∧ False)) → p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h7.left
      let h12 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h15.left
        let h18 := h15.right
        -- False on the left can always be used.
        apply False.elim h17
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h7.left
      let h21 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h22 =>
        -- False on the left can always be used.
        apply False.elim h21
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- Conjunctions on the left can always be decomposed.
        let h26 := h24.left
        let h27 := h24.right
        -- False on the left can always be used.
        apply False.elim h26
  case inr h28 =>
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h29 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h30
      -- Implications on the right can always be decomposed.
      intro h31
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h34.left
        let h36 := h34.right
        -- Conjunctions on the left can always be decomposed.
        let h37 := h33.left
        let h38 := h33.right
        -- Disjunctions on the left can always be decomposed.
        cases h37
        case inl h39 =>
          -- False on the left can always be used.
          apply False.elim h38
        case inr h40 =>
          -- Conjunctions on the left can always be decomposed.
          let h41 := h40.left
          let h42 := h40.right
          -- Conjunctions on the left can always be decomposed.
          let h43 := h41.left
          let h44 := h41.right
          -- False on the left can always be used.
          apply False.elim h43
      case inr h45 =>
        -- Conjunctions on the left can always be decomposed.
        let h46 := h33.left
        let h47 := h33.right
        -- Disjunctions on the left can always be decomposed.
        cases h46
        case inl h48 =>
          -- False on the left can always be used.
          apply False.elim h47
        case inr h49 =>
          -- Conjunctions on the left can always be decomposed.
          let h50 := h49.left
          let h51 := h49.right
          -- Conjunctions on the left can always be decomposed.
          let h52 := h50.left
          let h53 := h50.right
          -- False on the left can always be used.
          apply False.elim h52
    case inr h54 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h55
      -- Implications on the right can always be decomposed.
      intro h56
      -- Conjunctions on the left can always be decomposed.
      let h57 := h56.left
      let h58 := h56.right
      -- Disjunctions on the left can always be decomposed.
      cases h57
      case inl h59 =>
        -- Conjunctions on the left can always be decomposed.
        let h60 := h59.left
        let h61 := h59.right
        -- Conjunctions on the left can always be decomposed.
        let h62 := h58.left
        let h63 := h58.right
        -- Disjunctions on the left can always be decomposed.
        cases h62
        case inl h64 =>
          -- False on the left can always be used.
          apply False.elim h63
        case inr h65 =>
          -- Conjunctions on the left can always be decomposed.
          let h66 := h65.left
          let h67 := h65.right
          -- Conjunctions on the left can always be decomposed.
          let h68 := h66.left
          let h69 := h66.right
          -- False on the left can always be used.
          apply False.elim h68
      case inr h70 =>
        -- Conjunctions on the left can always be decomposed.
        let h71 := h58.left
        let h72 := h58.right
        -- Disjunctions on the left can always be decomposed.
        cases h71
        case inl h73 =>
          -- False on the left can always be used.
          apply False.elim h72
        case inr h74 =>
          -- Conjunctions on the left can always be decomposed.
          let h75 := h74.left
          let h76 := h74.right
          -- Conjunctions on the left can always be decomposed.
          let h77 := h75.left
          let h78 := h75.right
          -- False on the left can always be used.
          apply False.elim h77



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231283451103764609446760093628 : (((p5 ∨ p1) ∨ p3) → ((True ∧ (((p2 ∨ p4) ∨ True) ∨ p2)) ∨ (((p1 → (((p4 → False) → (p2 → p3)) → (p3 ∨ False))) → p4) → p5))) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328884317557910260062836407449 : (True → (((((p4 ∨ p2) ∨ p4) ∧ p2) ∨ (p4 ∨ p3)) ∨ (p3 → (False ∨ (p1 → (((False ∧ p1) ∧ p2) → (p4 ∧ (p3 ∨ (p1 ∧ p2))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
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
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h9 := h4.left
  let h10 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684499692843325808682573862340 : (((((((True ∨ p5) → p3) ∧ (False ∨ p4)) ∨ (p3 → ((p3 → (p4 ∨ (False ∧ p4))) ∨ p3))) ∨ (((True → (p1 ∨ True)) ∨ p5) ∧ p1)) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137882196008355380338424594563 : ((p4 ∨ ((((p4 ∧ True) ∧ (False ∨ (p1 ∧ (((p4 → p5) ∨ ((p1 → (p2 → p3)) ∨ p1)) ∧ p3)))) → p2) ∨ p1)) ∨ (p2 ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244111001601916281058457910258 : ((True ∧ p3) ∨ (False ∨ (p2 ∨ (p2 ∨ ((p4 ∨ ((p5 → (True → (p5 ∨ (((p2 → p5) ∧ p3) ∧ (p2 ∨ p3))))) ∨ p3)) ∨ (p1 ∧ p5)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693834134184005387745614589714 : (((((((False ∧ False) ∧ p3) ∨ ((p3 ∨ p4) → ((p5 → p1) ∨ p1))) → False) ∨ (((False ∨ (False ∨ (p5 ∧ False))) → (p5 ∨ p2)) ∨ p5)) ∨ False) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
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
      apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112053529567594649748017809266 : ((((False ∧ p1) ∧ (((p2 ∧ (p2 → (p3 ∨ p2))) ∧ ((p5 → ((p1 ∨ p4) ∧ (p4 → p2))) → (True ∨ p5))) ∧ p4)) ∨ False) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204800766677944100710709120067 : (((((p3 ∧ p1) ∧ p2) ∨ p4) → False) ∨ ((p1 ∧ (((p3 → (p5 ∨ p2)) ∨ p4) ∧ ((p3 → p2) → ((True ∨ False) ∨ p5)))) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55515401056870444083194526390 : ((((p4 ∧ p3) ∨ (p5 → (False ∨ p2))) → ((((p2 → (p2 ∧ ((p4 ∨ p3) ∨ True))) → False) ∨ (((p1 ∧ False) ∨ p1) → True)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173333324771919875208664636516 : ((p2 → ((p4 ∨ p2) ∧ (((True ∨ (False ∧ p5)) ∧ (p4 ∧ p4)) ∨ (True ∧ p1)))) ∨ (p3 ∨ (True ∧ ((p1 ∧ p1) → (p5 → (p1 ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118391234977191309723230084325 : ((p2 ∨ (((p3 → p3) ∧ (True ∨ True)) ∧ (((((p2 ∧ p5) ∧ p4) → p1) ∧ p3) ∨ ((p2 ∨ p3) → ((p3 ∧ p5) ∧ False))))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165887101024223960014283068958 : ((((p1 ∧ True) → p1) → (p3 ∧ (((p4 → p1) ∧ ((p5 → p4) ∨ (p2 ∨ False))) ∨ p1))) ∨ (((((p4 ∧ False) ∧ p3) ∧ p5) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179398390480036860416491102071 : ((p3 ∨ ((p4 ∧ False) ∨ ((True ∨ (p3 ∧ False)) → ((p1 ∧ p1) → p4)))) ∨ (p1 ∨ (((False → True) → (p4 → p2)) → ((p5 ∨ True) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689105467708775047298122719167 : (((((True → ((p1 ∨ (True → p3)) ∨ ((False ∨ ((False → p3) → p5)) ∧ p2))) ∨ False) ∨ (p4 ∨ ((p5 ∨ (p2 → (p1 → True))) → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217541271920934576868256986345 : ((((p5 → p4) ∧ True) → p1) → (p2 ∨ ((p1 ∧ ((p3 ∧ False) → (((False ∧ p1) ∧ p2) → ((p2 ∨ p1) ∧ p2)))) → (p5 ∨ (p1 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636132439351893678386397919343 : ((((((p3 → (True ∧ (((p4 → p1) ∧ ((p3 ∧ p3) → (False ∨ False))) ∨ p5))) ∨ p3) ∨ (((p5 ∧ p3) → p5) → (False ∧ p3))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44054927754098072543099717566 : ((((p5 → (((False → p1) → ((p1 ∨ p5) ∨ (p1 ∧ (p1 ∨ p5)))) ∨ (p2 → ((False ∧ (p4 ∨ p3)) ∧ p3)))) → (p1 → True)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133687988315168777803999981785 : (((((((True → False) → ((p1 ∧ p2) ∨ (p4 ∨ p2))) ∧ (p2 → p4)) → (p1 → p5)) ∨ (p2 → (True ∧ p5))) ∧ p3) ∨ ((p1 ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122286243275468989078816037955 : (((p4 ∧ ((True ∧ (p3 → (False ∧ p3))) ∧ (p4 ∧ ((p1 ∨ (p4 ∨ (p1 ∨ (p3 ∧ (p1 → p2))))) → p2)))) ∧ (p4 → p3)) → (p1 ∧ True)) := by
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
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h7.left
  let h11 := h7.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h12 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h13 := h3 h12
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h14 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h15 := h9 h14
  -- We need to get the left conjuct of h15 based on <expert-advice>.
  let h16 := h15.left
  -- False on the left can always be used.
  apply False.elim h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667594151744161016870886511239 : ((((p2 ∧ (((False ∧ (p5 ∧ ((p5 → (p5 ∧ (True → p5))) ∨ (((p4 ∧ p5) ∨ False) ∨ p3)))) ∧ False) ∨ p4)) ∧ (p3 ∧ (True ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135137441161950642590345331771 : (((False ∨ (((p3 → p2) → (((p2 ∨ p3) ∧ ((((p4 ∧ p3) → False) → True) ∨ True)) ∧ False)) ∨ False)) ∨ (False → True)) ∨ ((p4 ∧ p4) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69209269935729249905663544985 : ((p5 → ((p4 ∧ ((((p4 → p3) → p4) → True) → p3)) ∨ ((p4 ∨ p3) ∧ ((p1 ∧ p3) ∨ (((False ∨ (p3 ∧ True)) ∧ False) ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53090111248361870905728021397 : (((p1 ∨ ((p1 → p2) ∨ (((p4 → (p2 ∧ False)) → False) ∨ p2))) ∧ (p3 ∧ ((p1 → ((True ∨ (False → p2)) ∨ (p1 ∨ False))) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48122371513210198849773203978 : (((((False → p3) ∨ p2) ∧ (p3 ∨ (((((p5 → p5) ∧ (p5 ∨ p2)) ∨ ((p1 → (p3 → p4)) ∨ p5)) ∧ p1) → p4))) → (p5 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610671307795722737238605617946 : (((((((((False → (((p2 ∧ p4) ∧ p5) → (p4 → ((p4 ∧ True) ∨ True)))) → p3) ∨ True) → False) ∧ ((True → p3) ∨ p5)) → p1) ∨ p3) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (((False → (((p2 ∧ p4) ∧ p5) → (p4 → ((p4 ∧ True) ∨ True)))) → p3) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (((False → (((p2 ∧ p4) ∧ p5) → (p4 → ((p4 ∧ True) ∨ True)))) → p3) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196294769737223938487300309949 : ((p3 ∨ ((p1 → True) → (p2 ∨ (True ∨ p5)))) ∧ (((True → True) → p2) ∨ (p1 → ((p2 → (p1 ∧ p4)) → ((p2 ∨ p1) ∨ (False → p1)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183856911953403975631969557099 : ((((p5 → ((p1 ∨ p3) → (p3 ∨ p2))) → (p5 ∧ p3)) ∧ p3) ∨ ((p1 ∧ p1) → ((p4 → (p3 ∨ (False → p2))) ∨ (False ∨ (p3 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225369423431582644486971775118 : (((p2 ∨ True) ∧ p5) ∨ ((((p2 ∨ (p1 ∨ (p1 ∨ p2))) ∨ p5) → (p2 → ((p2 ∧ (p3 ∧ False)) ∨ p2))) ∧ (p1 ∨ (False ∨ (True ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254361309851518011607317389969 : ((p2 ∧ p4) → ((False ∨ (False ∧ p1)) ∨ (True → ((p2 → (p4 → (p3 → ((p3 ∨ False) ∧ (False ∨ False))))) → ((p4 → (p1 ∧ p5)) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245744004429094922071704284620 : ((p3 ∧ p2) ∨ (True ∧ ((p4 ∧ (((p2 ∧ (False ∧ True)) ∧ False) ∨ p1)) ∨ ((True ∧ (False → p1)) ∧ (False → ((p4 ∧ (True → p4)) → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253619754586457877528242935313 : ((p1 ∧ True) → ((((p1 ∧ p3) ∨ ((p5 ∨ p2) → ((p2 ∨ p4) → p3))) ∧ ((True ∧ (False ∧ p4)) ∧ p2)) ∨ (p5 ∨ ((p1 ∧ p3) → p3)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345958569588689093813626392791 : (p3 → ((((False → ((p2 ∧ p1) ∧ (p1 ∧ p5))) ∧ p2) ∧ ((p2 ∧ p5) ∨ (True → (True ∧ ((False → (p5 ∧ p5)) ∧ (p4 ∧ p4)))))) → p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38050168185446518401281143372 : (((((p1 ∧ ((((p1 ∨ p5) → True) ∨ (p2 → p4)) ∧ ((True → p4) ∧ ((p4 ∧ p4) ∧ p4)))) ∧ (p5 ∨ True)) → (p3 ∧ p5)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166031458581475840247304589087 : (((p1 → False) ∨ ((p3 ∨ ((False → ((p2 ∨ p1) → (True ∧ (p5 ∧ p2)))) → p4)) ∨ p5)) ∨ (p3 → (p3 ∨ ((False ∨ p4) ∨ (False → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213467549248372260128111384525 : (((False → (p4 ∧ p5)) ∧ p5) ∨ (((True ∨ p4) ∨ (True ∧ (p5 ∧ p2))) → (((p3 ∧ True) ∧ ((False ∧ ((p2 ∧ p1) → True)) ∧ p1)) ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180779863746838659442239851774 : ((((p3 ∨ p2) ∨ (True ∨ p3)) → (True ∧ (False ∧ (True → (True → p1))))) → (((p5 → (p3 → p5)) → p4) ∨ (p3 → (p4 ∨ (p3 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ p2) ∨ (True ∨ p3)) := by
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
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173829584023591645088354985176 : (((p4 ∨ ((p5 → p1) ∨ (((p1 → p4) → ((p4 ∨ p5) ∧ p2)) → p1))) ∨ True) → (True ∧ ((p2 ∨ p4) ∨ (p2 → (p2 ∨ (False ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h6
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158010874415723388826235983177 : (((((p1 ∧ (p1 ∨ p3)) → p5) ∨ p5) ∧ ((p3 ∨ (p3 ∧ p2)) ∨ (((True ∧ p3) ∨ p2) ∨ p1))) ∨ (p4 → ((p5 ∧ False) → (True ∧ p5)))) := by
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
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39338039146728379569688234016 : (((p2 ∧ (((p1 ∨ p3) → p4) → (((p5 ∧ ((p2 ∨ p3) ∧ ((p2 → (p1 ∧ p4)) ∧ p2))) ∨ (p4 → (p1 ∨ p3))) ∨ p1))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739128073860167634263562078466 : ((((p3 ∧ p5) ∨ (p4 → (False ∨ ((p5 ∧ ((((p1 → (((p5 ∨ p2) ∧ (True → p2)) ∧ p1)) ∨ (p1 ∨ p1)) → True) ∨ False)) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



