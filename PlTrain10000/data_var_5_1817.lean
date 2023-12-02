variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80809718272238850460462926335 : (((p5 → (((p4 ∧ p5) ∧ (p2 → p4)) → (True → ((p5 → False) → (p2 ∧ (p2 ∧ (p5 ∨ ((p1 ∧ p5) ∨ p3)))))))) → (False ∧ p3)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → (((p4 ∧ p5) ∧ (p2 → p4)) → (True → ((p5 → False) → (p2 ∧ (p2 ∧ (p5 ∨ ((p1 ∧ p5) ∨ p3)))))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h7 := h4.left
    let h8 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h11 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h12 := h6 h11
    -- False on the left can always be used.
    apply False.elim h12
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h13 := h4.left
    let h14 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h17 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h18 := h6 h17
    -- False on the left can always be used.
    apply False.elim h18
    -- Conjunctions on the left can always be decomposed.
    let h19 := h4.left
    let h20 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h23 := h1 h2
  -- We need to get the left conjuct of h23 based on <expert-advice>.
  let h24 := h23.left
  -- False on the left can always be used.
  apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252590678918533304279652220737 : ((p5 → p3) ∨ ((p1 ∧ ((p4 ∨ (p2 ∧ ((False ∧ (p3 ∨ True)) → (p2 ∨ False)))) → p4)) ∨ ((p5 ∨ (False ∨ ((p1 ∧ True) → p5))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310763461243122857825524158659 : (p2 ∨ (((True ∧ False) ∧ p5) ∨ (p3 ∨ ((p1 ∨ ((False ∨ ((True → False) → (p3 → p1))) ∧ (p4 → ((p3 ∨ (True ∧ p4)) ∨ False)))) ∨ False)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134767853863275468703593647312 : (((True ∧ ((((True → (((p1 → True) → (False ∨ (p2 ∨ True))) ∧ (p3 ∧ p1))) → (p3 ∧ p1)) ∧ p1) ∧ p3)) → p4) ∨ (False → (p3 ∧ p5))) := by
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
theorem thm_5_vars_148525182161452383200958312483 : ((((((p4 ∧ True) ∨ (p2 ∨ p4)) ∨ p4) ∨ ((p4 → False) → p1)) → (p1 → ((p1 ∧ (p1 ∧ p2)) ∨ True))) ∨ (p1 ∨ ((p4 ∧ False) ∧ p4))) := by
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
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137183490970182425969533023331 : ((False ∧ (((p2 ∨ True) → (p5 → (p4 ∧ False))) → ((p1 ∧ ((p4 ∨ False) ∨ (True ∧ p1))) ∨ (True → (p1 ∨ False))))) ∨ ((p5 → p5) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616015746714980021804303934150 : ((((((p5 ∧ (p4 → (p3 → p1))) ∨ (((p1 → False) ∨ (p1 ∧ False)) ∨ p1)) → (((p2 ∧ False) ∧ (p1 → (True ∨ p3))) ∧ True)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50243457505748185132585670144 : ((((((((p4 ∨ False) ∨ p4) → p3) ∧ (p4 ∧ (p4 ∧ (True → p4)))) ∨ (p4 ∨ (p1 ∨ p2))) → False) ∨ (p3 → (False → (False → True)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113212078600284327716121998484 : (((((p1 ∨ False) ∨ ((True ∧ (True ∧ ((p3 → (False → p1)) → ((p3 ∧ False) ∨ (p5 ∧ p3))))) ∧ p1)) ∨ p5) ∧ (p2 ∨ p5)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65151085490646797860866682335 : ((p2 ∨ (p5 → ((((p4 → ((p3 ∧ (p2 ∨ (((p1 ∨ True) ∧ p5) → ((p2 ∧ False) ∨ (False → p3))))) ∧ p2)) ∨ False) ∧ p3) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739023469192020413828967141224 : ((((p3 ∧ p3) ∨ ((p3 ∧ ((((p2 ∨ (False ∨ p2)) ∨ True) ∧ p3) ∧ ((((p5 ∧ p1) ∨ (p5 → True)) ∨ p3) ∧ True))) ∨ (p4 → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149234473890837773703578107215 : (((p5 ∧ p4) ∨ ((True ∧ ((((p3 ∨ (p4 ∧ True)) → (p3 → p3)) ∧ p3) ∨ (True ∨ (p4 ∧ p5)))) ∧ False)) ∨ (p1 ∨ (p1 → (True ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147430089704570182579495118597 : (((((False ∧ False) ∨ True) → (((p4 ∧ p5) ∧ p2) ∨ ((p5 ∧ (p2 ∧ (p4 → p2))) → (False ∧ True)))) ∨ p4) ∨ (p1 → ((p4 ∧ p5) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118742272415422591126235526117 : ((p5 ∨ (((p2 ∨ True) ∧ ((p5 ∨ p3) ∨ p5)) ∧ ((p4 ∨ (((p5 ∨ ((p3 ∨ p4) ∨ (p5 ∨ True))) ∨ p4) ∨ False)) ∨ False))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179058020199145597729671745708 : ((True ∧ ((((((p5 ∧ (False ∧ False)) ∨ p1) ∧ p4) ∧ p2) ∧ p4) ∧ True)) ∨ (p5 ∨ (False → (((((False ∧ p3) ∨ True) ∨ p4) ∨ p5) ∧ p1)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587928540777197112066863656066 : ((((((p2 ∧ (p4 ∨ ((True ∧ ((True ∧ ((p5 ∨ (True → False)) ∧ True)) ∧ True)) → (p2 → True)))) ∧ (p5 ∨ (True ∧ p2))) ∨ p1) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309307466025689975950700021954 : (p2 ∨ ((((p5 ∨ ((True → False) ∨ ((True ∨ (p3 ∧ True)) → (p4 ∨ ((p5 → ((p4 → p5) → p1)) ∨ False))))) ∧ p5) ∨ True) ∨ (True ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62633933310839562242682915741 : ((p4 ∧ ((True ∧ ((((True → (p2 ∧ (p4 → (((p2 → p5) ∧ p5) → ((p1 → True) → p1))))) ∧ p5) ∨ (p4 ∨ p1)) ∨ p5)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178901767016146192530693033959 : (((p2 ∨ p5) ∧ ((((p4 ∧ p1) → p4) → True) ∨ ((p4 ∨ p5) → p3))) ∨ ((((False ∧ (p1 ∧ p5)) ∧ p4) ∨ ((p5 → False) → True)) ∨ False)) := by
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
theorem thm_5_vars_207810985554118993327977981632 : (((p2 → (p4 → (p5 ∨ True))) → True) → (p1 ∨ ((p3 ∧ p4) ∨ ((False ∨ ((((p2 ∨ p2) ∨ True) ∨ p3) ∨ (p5 → (p2 ∧ True)))) ∨ p3)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137756321098821396764862171278 : ((p2 ∨ (((p4 ∨ (p1 ∨ (((False ∧ p2) ∨ (True ∨ p2)) → (True ∨ (((p2 ∨ p4) → p3) ∨ p2))))) → p5) → p1)) ∨ ((True ∧ True) ∨ False)) := by
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
theorem thm_5_vars_78616127408169052340586332591 : ((((((p2 ∨ (p4 ∨ (p2 ∨ True))) ∨ (((p3 → (p1 ∧ (p2 ∨ p1))) → True) ∨ True)) ∧ (p2 → True)) → (False ∧ p1)) ∧ (False ∨ p1)) → p2) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (((p2 ∨ (p4 ∨ (p2 ∨ True))) ∨ (((p3 → (p1 ∧ (p2 ∨ p1))) → True) ∨ True)) ∧ (p2 → True)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h6
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_93865334524835561804638320639 : ((p1 ∧ ((p5 ∨ (((((p5 ∧ p4) ∨ (p1 ∨ False)) ∨ p1) ∨ (p5 → ((False ∨ p5) → False))) ∧ p5)) ∧ ((p3 → (p3 ∨ False)) → False))) → False) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (p3 → (p3 ∨ False)) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h7
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
        cases h14
        case inl h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h18 : (p3 → (p3 ∨ False)) := by
            -- Implications on the right can always be decomposed.
            intro h19
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h19
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h20 := h5 h18
          -- False on the left can always be used.
          apply False.elim h20
        case inr h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h22 =>
            -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
            have h23 : (p3 → (p3 ∨ False)) := by
              -- Implications on the right can always be decomposed.
              intro h24
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h24
            -- We have shown the premise of h5, we can now drive its conclusion.
            let h25 := h5 h23
            -- False on the left can always be used.
            apply False.elim h25
          case inr h26 =>
            -- False on the left can always be used.
            apply False.elim h26
      case inr h27 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h28 : (p3 → (p3 ∨ False)) := by
          -- Implications on the right can always be decomposed.
          intro h29
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h29
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h30 := h5 h28
        -- False on the left can always be used.
        apply False.elim h30
    case inr h31 =>
      -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
      have h32 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h31, we can now drive its conclusion.
      let h33 := h31 h32
      -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
      have h34 : (False ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h33, we can now drive its conclusion.
      let h35 := h33 h34
      -- False on the left can always be used.
      apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63945257066133954383866785484 : ((False ∨ (((False ∨ (p1 ∧ p5)) → (((((p5 ∧ p1) ∨ (((False → True) ∨ (p2 → p4)) ∨ False)) ∨ p5) → p2) ∧ (p4 ∨ p5))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_472230279037735138726224907222 : (((((p4 ∨ p2) ∨ (True ∧ (((p1 → p3) → (p5 → False)) ∨ True))) ∨ (p3 ∨ (((p4 → (p4 → True)) → True) ∨ (False ∧ (True ∧ p5))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51163253040478079279716672486 : (((((((((p1 → False) → p1) → p5) ∨ p5) ∨ p3) ∨ ((p3 → False) ∨ p1)) ∧ (p4 → False)) ∨ ((False ∧ False) → ((True ∨ False) → p3))) ∨ p2) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136228925477379158799199714671 : (((((False → True) ∧ p2) ∧ (p5 ∨ p4)) ∨ (p1 ∨ (((((True ∨ p2) → p5) ∧ True) ∧ ((p5 → True) ∧ True)) ∨ True))) ∨ ((p5 → False) ∨ p4)) := by
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
theorem thm_5_vars_165421541685624255660281214450 : ((((True ∨ (((p3 ∨ p5) → p2) → p1)) → (p1 ∧ (True ∨ p4))) → (p3 → (True → p2))) ∨ ((((p5 → True) → p3) ∨ (True ∨ p3)) ∧ True)) := by
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
theorem thm_5_vars_732069276098825695923665538276 : ((((True ∧ p1) ∧ ((p1 ∨ p5) ∧ ((((p1 ∨ (p4 → p4)) → ((p3 ∨ (p4 ∧ p4)) ∧ (p1 → p4))) → p1) → (p1 → (p2 ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353471042963839233637032886110 : (p4 → (p2 ∨ ((((p5 → p4) ∧ (((((p4 ∨ ((p3 ∨ p3) ∧ p4)) → p3) ∨ (p4 → (p3 ∨ p2))) ∨ (p2 ∨ p4)) ∨ p5)) ∨ p3) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136675237294289640455258622936 : (((p5 ∨ (p4 ∨ p2)) → (((True → p1) → (p1 ∨ p4)) → (p2 ∧ (p3 → ((p2 ∧ (p1 → (p1 ∧ False))) → p1))))) ∨ ((p1 ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114101696729864068668647863562 : (((p3 ∧ ((p1 → ((p2 ∧ ((True → p1) → p3)) ∨ ((((p4 ∧ False) ∨ True) ∨ p5) ∨ p2))) ∨ False)) ∨ (p1 → (True ∨ p1))) ∨ (p1 ∨ False)) := by
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
theorem thm_5_vars_648747289440416535644954506443 : (((((p5 ∧ (((p1 ∧ p1) ∧ (p3 ∨ ((((p4 ∨ (p2 ∨ (p1 → p5))) → p5) → (p1 ∨ p1)) ∧ p3))) ∧ p4)) ∨ True) ∧ (True ∨ p4)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116555905621783272110641143164 : (((p1 ∨ p3) ∧ (True → (False ∨ ((((p4 ∧ True) → p5) ∧ False) ∧ (p3 → (False ∨ ((((p5 ∨ p1) ∧ True) → p4) → p3))))))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194078403677417750704003973503 : ((True → ((False ∨ (p5 → False)) ∧ (p5 ∨ (p1 ∧ False)))) → (p2 ∨ ((p5 → p2) → ((False ∨ False) ∨ (((p4 → (p2 → p1)) → p1) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
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
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157454976620666767210637231159 : (((((p4 ∧ (p3 → (p1 ∨ (((p3 → p4) → p3) → p2)))) → (p5 ∨ p3)) ∧ p3) ∨ (False → p4)) ∨ (((p3 → (p5 ∧ p1)) → p5) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201127119818542111060025082851 : ((True → (p1 → (((False → p2) ∧ p3) → p1))) → ((((p2 ∨ (p4 ∧ (((p2 ∧ True) ∨ p1) ∧ p2))) ∨ p1) ∧ p2) → (p2 ∧ (False → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h16 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Implications on the right can always be decomposed.
  intro h17
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303851224108173415244809890372 : (p1 ∨ ((((True ∧ (p3 → True)) → (p4 ∧ ((p5 → p1) ∧ (((p2 ∨ p2) → ((True → p5) ∨ (p4 → p4))) ∨ p5)))) → (p3 ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228002192052356247655768044707 : ((p3 ∧ (True → True)) ∨ (p1 ∨ ((((True → False) ∧ (p1 ∧ ((False ∨ (False → p2)) ∧ ((p4 ∧ p4) → ((False → p1) ∧ p4))))) ∨ True) ∧ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744849822908550876436435303564 : ((((p3 ∧ p4) → (((((p1 ∨ False) ∨ p4) ∨ p2) ∧ ((p1 → p1) → (((p4 → (True ∨ p2)) ∨ (p3 → p1)) → p2))) → (False ∨ p2))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h1.left
        let h9 := h1.right
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h10 : (p1 → p1) := by
          -- Implications on the right can always be decomposed.
          intro h11
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h12 := h4 h10
        -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
        have h13 : ((p4 → (True ∨ p2)) ∨ (p3 → p1)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h12, we can now drive its conclusion.
        let h15 := h12 h13
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h1.left
      let h19 := h1.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h20 : (p1 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h21
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h22 := h4 h20
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h23 : ((p4 → (True ∨ p2)) ∨ (p3 → p1)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h24
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h25 := h22 h23
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h25
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h1.left
    let h28 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h26
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192722069279708559352625822049 : (((((False ∧ p5) → False) → ((p5 ∧ p2) ∧ p5)) → p1) → (p5 → (((False ∧ (p1 → p2)) ∧ (False ∨ (((False ∧ p3) ∧ p5) → p2))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245948727889390630182275415645 : ((p4 ∧ True) ∨ (((p4 ∨ ((p3 ∧ ((((p3 → ((p5 ∧ p4) ∨ p4)) → p5) ∨ p5) ∨ p3)) ∨ (((p3 ∨ p2) ∧ p4) ∧ True))) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_982245565106836430124478545463 : (((p1 ∧ ((((p1 ∨ True) → False) ∧ (p1 ∨ (((p5 → (p3 ∨ ((p1 → (True ∧ (p4 → p1))) ∨ p5))) ∨ p2) ∨ (p5 ∨ p3)))) ∨ False)) → p2) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : (p1 ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h9 := h5 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h13 : (p1 ∨ True) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h2
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h14 := h5 h13
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- One of the premise coincides with the conclusion.
          exact h15
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h18 : (p1 ∨ True) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h2
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h19 := h5 h18
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h21 : (p1 ∨ True) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h2
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h22 := h5 h21
          -- False on the left can always be used.
          apply False.elim h22
  case inr h23 =>
    -- False on the left can always be used.
    apply False.elim h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192754415212216229482230508871 : (((True ∧ (((p2 → (p3 ∧ p1)) → True) ∨ True)) → p5) → (((False ∨ p5) ∧ ((p1 ∨ ((p2 ∨ False) ∧ (p3 ∨ (True ∨ p1)))) → p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53366653287381374617332990692 : ((((True ∨ ((True ∨ ((True ∨ p4) → p4)) ∨ (p5 ∨ p4))) ∨ p1) → (p5 ∨ (p3 → ((((p4 ∧ (p3 ∨ False)) → p1) ∧ p2) → p3)))) ∨ False) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h11
          -- Implications on the right can always be decomposed.
          intro h12
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- Implications on the right can always be decomposed.
          intro h17
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- One of the premise coincides with the conclusion.
          exact h16
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h23
          -- Implications on the right can always be decomposed.
          intro h24
          -- Conjunctions on the left can always be decomposed.
          let h25 := h24.left
          let h26 := h24.right
          -- One of the premise coincides with the conclusion.
          exact h23
  case inr h27 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h28
    -- Implications on the right can always be decomposed.
    intro h29
    -- Conjunctions on the left can always be decomposed.
    let h30 := h29.left
    let h31 := h29.right
    -- One of the premise coincides with the conclusion.
    exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154145620099429382721712193621 : ((((((p5 → p5) → p5) ∧ (((p3 → ((True ∨ True) ∨ p3)) → p3) ∧ (p1 ∧ p4))) ∨ p3) ∨ True) ∧ (True ∨ (p4 → ((False ∨ p4) ∧ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133859815752797430204107895201 : (((p1 ∧ (p2 ∨ (((False → (p2 ∧ ((p2 ∧ ((((p1 ∧ True) → p4) ∧ p3) → p3)) ∧ True))) ∨ p2) → p3))) ∧ p3) ∨ (p1 → (p4 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140874026828469247518239394272 : ((((p4 → (p5 ∨ p2)) ∨ ((p3 ∨ True) ∨ (True ∨ (p4 → p5)))) → ((p4 ∧ (p2 ∧ ((p5 ∧ False) → False))) ∨ p1)) → ((p1 ∧ p1) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 → (p5 ∨ p2)) ∨ ((p3 ∨ True) ∨ (True ∨ (p4 → p5)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h9
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789919325039955515413190085169 : (((p5 ∨ ((True → (p5 ∨ p2)) → (p1 → ((p2 ∧ True) ∨ (p4 ∨ ((p5 ∨ (p1 ∧ (True ∧ (p1 → p4)))) → ((p2 ∨ False) ∨ p5))))))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h10
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148369644949350108540808901342 : (((((((False → p5) ∧ (p3 ∨ p3)) ∨ (p2 → p5)) ∧ (p5 ∨ p5)) ∨ p3) ∨ (False ∨ ((p1 ∨ p1) ∨ p2))) ∨ (p1 ∨ (p1 ∨ (p5 ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616687896029039278986021337585 : ((((((True ∧ ((True ∧ p3) ∧ ((p5 → True) ∨ p1))) ∧ p5) ∨ (p5 ∧ ((p5 ∨ True) ∧ (p5 ∨ (p1 ∨ (p5 ∨ (p5 ∨ p2))))))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191463904131987450861163696164 : (((p5 → p1) → (((p2 → False) ∧ p3) ∧ (p1 ∧ p3))) ∨ ((p2 ∨ (((p3 ∨ ((True ∨ p1) ∧ p2)) → (p4 → True)) → (p2 ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14588374145548828977518142228 : ((((p1 → (p4 ∧ ((((p3 ∧ ((((False → ((p2 → p4) ∧ p5)) → False) ∧ p4) ∨ p5)) → False) ∨ p2) ∨ p3))) ∨ True) ∨ (p2 → True)) ∧ True) := by
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
theorem thm_5_vars_304681159557237918382307925269 : (p1 ∨ (((p4 ∧ (((True ∧ (True ∨ (p3 ∧ p5))) ∧ ((p1 ∧ (True ∧ (p5 → False))) ∨ (p4 → p5))) ∨ (p4 → p2))) ∧ p1) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763392542104946816053089570941 : (((p3 ∧ (True ∧ ((((True ∨ (True → ((p1 ∨ p1) ∨ p3))) ∨ p2) ∧ (True → (p1 ∨ (p5 ∧ p5)))) → ((p1 → False) ∧ (True → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228109921756689362270578659213 : ((p4 ∧ (p4 ∨ False)) ∨ (p2 → ((((p3 ∧ p5) ∧ p5) ∨ ((False ∧ (p3 ∨ (True → (False ∧ p3)))) ∨ ((False → (p1 ∨ True)) ∧ p1))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261278130585124734312136377398 : ((p5 → True) → ((True → (True ∧ (False ∧ (True → ((p3 ∨ False) ∨ p2))))) → (p3 ∨ (((p4 → (p4 ∧ p1)) ∧ p2) → ((p1 ∨ p3) ∧ p2))))) := by
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
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173578771635688286428332994873 : ((((p3 ∨ p5) → ((False ∨ ((p5 ∧ p2) ∧ (p1 → (p4 ∧ p2)))) ∨ p1)) ∧ True) → ((p5 → p2) → ((p5 ∧ (p4 ∧ False)) ∨ (False → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160486127675798514668660493012 : (((((True → (p2 ∧ (False ∧ False))) → ((False ∧ p5) ∧ p4)) ∧ p3) ∧ ((True → (False ∧ p4)) → p4)) → ((p4 ∨ (p4 → True)) ∨ (p1 ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119278023369327588425149376240 : ((p3 → ((False ∨ ((p5 → ((p4 ∨ (p1 ∨ (True → p3))) ∨ p4)) → ((p5 ∧ p3) ∨ (((p3 → p5) ∧ False) ∧ False)))) ∧ False)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180200237578907127324661350817 : (((((p1 ∨ p1) ∨ p3) → ((True ∧ (p4 ∨ p1)) ∧ (p2 ∧ p2))) → p4) → (((True → (p2 ∨ (p3 → (p5 → (p4 ∨ True))))) ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300128546206736512856054990901 : (False ∨ (((p1 ∧ False) ∨ (p4 → (((p5 → p3) ∨ ((p1 ∧ True) ∧ p2)) ∨ ((p5 ∨ (False → (p3 → (p3 ∨ p4)))) ∨ p3)))) ∨ (False ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345449617596978206154975663838 : (p3 → (((p5 ∧ (p2 ∨ ((p5 ∨ p2) ∨ ((p1 → p4) ∨ ((True ∧ False) ∧ (False → ((p2 → (p3 → True)) ∧ p2))))))) ∨ (True ∨ p4)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175233556176492219401188687674 : ((p1 ∨ ((True ∧ (p4 ∨ p1)) ∧ (True → (p1 ∧ ((p3 ∧ p4) ∧ (p1 ∨ True)))))) → ((((p1 ∧ p1) ∨ ((p5 → True) → p1)) ∧ p1) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
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
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h9
      -- One of the premise coincides with the conclusion.
      exact h9
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246572951864093673674444618260 : ((p5 ∧ p2) ∨ (((p2 → (p4 ∧ p2)) ∧ ((p1 ∧ (True ∧ True)) ∧ ((p2 → (p1 ∨ True)) ∧ ((False → p2) ∧ p5)))) ∨ ((p1 ∨ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245405941101003581917509868342 : ((p2 ∧ p4) ∨ ((p1 ∧ ((p4 ∧ (p1 ∨ p5)) ∨ (((p5 → p4) ∧ p2) → ((p2 ∧ (p2 → ((True ∨ p4) ∧ p4))) ∨ (p3 ∨ p3))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57927767659803621430492452559 : (((True → (p1 ∨ True)) → ((((((p2 ∧ p2) ∨ False) → (p1 ∨ (((p4 ∧ True) → p1) ∨ ((p3 ∧ p2) → p2)))) ∨ p5) ∧ False) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351210800137147334377418557458 : (p4 → (((p5 ∨ ((p5 ∧ (p1 → (p2 ∨ ((((((p1 ∨ p1) ∨ p2) ∨ p2) ∧ p1) ∧ p4) ∧ p2)))) ∨ p1)) ∧ p2) ∨ ((True ∧ False) → p3))) := by
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
theorem thm_5_vars_86100126130300588138852241200 : (((p4 → (((p3 ∧ p2) → (p1 ∧ True)) → (p4 ∧ p5))) ∧ ((p2 ∧ p1) ∧ (True ∧ (p4 ∧ ((p4 ∧ (p5 ∨ p4)) ∨ (p5 → p3)))))) → p5) := by
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
  let h8 := h5.left
  let h9 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h17 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h17
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h19 : ((p3 ∧ p2) → (p1 ∧ True)) := by
        -- Implications on the right can always be decomposed.
        intro h20
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- One of the premise coincides with the conclusion.
        exact h7
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h23 := h18 h19
      -- We need to get the right conjuct of h23 based on <expert-advice>.
      let h24 := h23.right
      -- One of the premise coincides with the conclusion.
      exact h24
  case inr h25 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h26 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h27 := h2 h26
    -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
    have h28 : ((p3 ∧ p2) → (p1 ∧ True)) := by
      -- Implications on the right can always be decomposed.
      intro h29
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- One of the premise coincides with the conclusion.
      exact h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h27, we can now drive its conclusion.
    let h32 := h27 h28
    -- We need to get the right conjuct of h32 based on <expert-advice>.
    let h33 := h32.right
    -- One of the premise coincides with the conclusion.
    exact h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229088170183931590748862697072 : ((p5 ∨ (p3 → False)) ∨ (True ∧ (p4 ∨ ((((((p5 ∧ (p2 ∧ (p3 ∧ p5))) ∨ (p5 → p1)) ∨ ((True ∧ True) ∧ p1)) → False) ∧ True) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_604204271480221442764529085633 : ((((True → (((True ∧ p4) → (p1 ∨ (p4 → (True ∧ (((p1 ∧ (p2 → (p5 ∨ (p2 → (p2 ∨ p2))))) ∧ False) ∧ p4))))) ∧ p3)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622480595484828911057883339677 : ((((p3 ∧ (p4 ∧ ((p5 ∨ p1) ∧ (p1 → (p2 → (((((True → p3) ∧ (p1 → True)) → ((p1 → p2) ∧ True)) ∧ p2) ∧ False)))))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_147130150670602329786460994594 : ((((p2 ∨ p5) → ((p2 → p5) ∨ (p1 ∧ ((True ∨ ((p1 ∨ False) ∨ p2)) ∨ ((True ∨ p4) ∨ True))))) ∧ p3) ∨ (((p4 → p4) ∨ p2) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609466905967011488996410587959 : (((((False ∧ ((p3 ∨ ((((p1 ∨ True) ∧ p4) → (((p2 ∨ p5) ∧ (True ∧ p5)) ∨ (False → p4))) ∧ p1)) ∨ (True ∨ True))) ∨ p3) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71099931193478003540243957225 : ((((p4 → ((p1 ∧ (p1 ∧ p2)) ∨ True)) → ((p2 ∨ False) ∧ (p5 ∧ ((((p3 → p2) ∧ p4) ∨ (False ∨ (p1 → p2))) ∧ False)))) ∧ True) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p4 → ((p1 ∧ (p1 ∧ p2)) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67700262976127071659621606375 : ((p1 → (p4 → (False ∨ ((((True → p5) ∧ (p3 ∧ True)) ∧ p5) ∧ (((((p5 ∨ True) ∧ True) → (p3 ∧ (True → p2))) ∨ p4) → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623886468367611066233261150813 : ((((p1 ∨ (p5 ∨ ((p1 ∨ (p1 ∧ ((False → False) → ((p1 → (((False → p5) ∧ True) ∨ (p3 → True))) ∨ p3)))) ∨ (p2 ∨ p3)))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111663497818187838841370942251 : ((((False ∨ ((((True ∧ p4) → (True ∧ p2)) ∧ ((False ∧ ((p1 ∨ p1) ∨ (p3 ∧ (p1 ∧ p2)))) ∨ p2)) → p4)) ∨ False) ∨ p2) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323999299749565052086208897779 : (p5 ∨ (((True ∨ p4) → (((p4 ∨ (p2 ∧ False)) ∨ False) ∨ (False → (p1 ∧ True)))) ∨ (p4 → ((False → p4) ∨ ((p3 → False) ∨ (p2 → False)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46927152433119275224728915465 : (((((p3 ∨ False) ∧ (((p3 ∧ p3) ∧ ((False ∧ ((True → p2) → (((True → True) ∨ p4) ∨ False))) → p3)) ∧ p5)) ∨ p4) ∨ (p5 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301694823608825885082257835847 : (False ∨ ((False ∨ True) ∧ ((p4 ∨ ((p2 ∧ p3) ∧ (False ∨ (True → ((p3 ∨ (p1 ∨ p4)) ∨ p4))))) ∨ ((p3 ∨ (p1 → (False ∨ p1))) ∨ p4)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315101596559944899308928053884 : (p3 ∨ ((False → (((p5 ∨ p4) ∧ p3) ∨ p1)) ∧ ((p1 ∨ (p4 ∨ ((p5 ∧ (True ∧ (p5 → p3))) → (p3 ∨ False)))) → ((p2 ∨ p4) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
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
theorem thm_5_vars_218661693694825223576957808851 : ((True ∧ (p2 ∧ (p5 → p1))) → (((p1 ∨ ((p1 ∨ p1) ∨ p1)) ∨ p5) ∨ (((p5 ∧ (p2 ∨ False)) ∨ (p5 ∨ p2)) → (p3 → (p2 ∨ True))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157068739663587024261194509207 : (((False ∨ (((True ∧ ((True ∧ (p3 → True)) ∨ p3)) → (False → (p2 → (p4 ∧ True)))) → p2)) ∨ True) ∨ (((p1 → p3) ∧ (p3 → False)) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180951159314578944993651348220 : (((p3 ∨ p2) ∧ ((((False ∨ p1) → p5) → (True ∨ (p5 → True))) → p5)) → (((p5 → ((p4 ∧ True) ∨ p1)) → False) ∨ ((p4 ∨ True) ∨ p2))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165701158630216828013139483914 : (((((p2 ∧ p2) ∨ False) ∧ p3) ∧ ((p1 ∧ (p3 ∨ p2)) ∧ ((p1 ∨ False) ∧ (p1 ∨ p2)))) ∨ ((((False → p1) → p3) ∧ False) → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119215025440787311684451813850 : ((p2 → ((False → (p5 ∧ ((p3 → p2) → p4))) ∧ ((((p3 ∧ (False ∨ (p3 ∧ False))) → ((p5 ∧ True) ∨ p1)) → False) ∨ True))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146914614125860032280301357408 : ((((((((((p2 ∧ p4) → p5) ∧ p5) ∧ p2) ∧ True) → False) ∨ ((p4 → True) ∨ (p5 ∧ p5))) ∧ p1) ∧ False) ∨ ((False ∧ p5) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55511953642308043046859791153 : ((((p5 → p5) ∧ ((p3 → True) ∨ p4)) → (((((((False ∨ p2) ∧ False) ∧ p3) ∨ ((p4 ∧ p3) ∨ p5)) ∧ p3) ∨ (p2 → True)) ∨ p1)) ∨ p5) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113895765769511151739975479880 : (((((True ∧ (p3 ∨ (((True ∧ ((p3 ∨ p5) ∧ p4)) ∨ p1) ∨ ((p4 ∨ p1) ∨ p5)))) ∧ True) → p4) ∧ (p1 ∧ (p5 ∧ p5))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66412277121721798803285020915 : ((p5 ∨ (p2 → ((p5 ∧ (p5 → (p3 → p3))) ∨ (p2 → ((((p2 ∨ (((p4 ∧ p5) ∧ (p2 ∧ p2)) ∨ False)) ∨ p5) ∧ p1) ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348241117390161896984770002579 : (p3 → (True ∧ (((((p5 ∨ p1) → ((p1 → ((True ∨ (p2 ∧ p2)) ∨ False)) ∨ p1)) ∨ ((p4 ∨ p3) ∧ ((p5 ∨ False) ∧ True))) → p4) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40995552384544201859355694974 : ((((True → (((p3 ∧ (p5 ∧ (True → ((False ∧ p2) ∨ True)))) → (p5 ∧ ((p3 → (p2 ∧ p4)) ∨ p5))) → p3)) ∨ (p2 → p2)) ∨ p2) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323657122459427330556674669040 : (p5 ∨ ((((((p2 ∧ p2) → p2) ∧ (p1 → True)) ∨ (((p4 ∨ p3) → p5) → ((p2 → p2) ∨ p5))) → p3) ∨ (p4 → ((p5 ∧ p1) → True)))) := by
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
theorem thm_5_vars_113317607778922669960092557323 : ((((True ∧ (p5 ∧ False)) ∨ ((p4 ∨ ((p1 ∧ (p4 → True)) ∧ ((True ∨ ((True ∧ p4) → p4)) ∧ p2))) ∨ p2)) ∧ (p4 ∨ p2)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53167055348573318305023039347 : (((((((False ∨ (p3 ∧ p5)) ∨ p5) ∨ (False → p1)) ∧ True) → False) ∨ ((((p3 → True) ∨ (((p5 ∧ p2) → True) → p4)) ∨ p2) ∨ p1)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164597403409831031055304910642 : ((((p1 ∨ p5) → ((p3 ∨ (p4 ∧ ((p1 ∨ (p1 → p3)) ∨ (p1 ∧ p4)))) ∧ p5)) ∧ p1) ∨ ((p4 → p4) ∧ (p5 → (p4 → (p4 ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214050162176341894578152242993 : ((((False → p2) ∧ True) → p3) ∨ (p2 → (((p5 ∧ p1) → ((True → (((p5 → False) ∨ (p3 → p4)) ∧ True)) ∨ (False ∨ (p1 ∨ p5)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148288026973867355866497207704 : (((((((p1 → ((p1 ∨ p5) ∨ True)) → (True ∧ p2)) ∧ p5) ∧ True) ∨ (p5 → False)) → ((p5 ∧ p1) ∨ p3)) ∨ ((p4 ∨ p5) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118245387556582722298247925866 : ((p1 ∨ ((((((p2 → True) ∨ (True → ((p3 ∧ ((p3 → p4) ∧ True)) → False))) ∨ (p1 → p4)) ∧ p4) ∧ True) → (p5 → p1))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



