variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41928961782859409526302267905 : ((((p2 ∨ (p5 → False)) → (((p1 → p3) ∧ (p3 ∨ (((False ∧ p2) → (((False ∧ p5) ∨ (p3 ∨ p1)) ∨ True)) ∨ False))) → p5)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673308761491162218599158141146 : ((((((True ∨ p2) ∧ (p3 ∧ (p1 ∧ (True → p1)))) → ((((p3 ∨ False) ∨ True) ∨ (True ∧ (p5 ∨ p2))) ∧ p1)) → (p3 ∨ (p4 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247364415287186341484882005688 : ((False ∨ p1) ∨ ((((p1 ∨ (p4 ∨ (p2 ∨ p1))) ∧ ((p1 → (((p4 ∨ p5) ∧ p1) ∨ p4)) ∧ True)) ∨ p1) ∨ (False → (p1 ∧ (True ∨ True))))) := by
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
theorem thm_5_vars_733116162740177216079545246249 : ((((p3 ∧ False) ∧ (((p2 ∨ False) ∨ (((((((False → p5) ∧ ((p5 ∧ p5) ∨ p3)) ∧ True) ∧ p2) ∧ p2) → (False → False)) ∨ p2)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668826077748443007191120886403 : ((((((((p1 → (True ∨ p2)) ∨ p3) ∧ (True ∧ (p1 ∨ False))) → ((((p5 ∧ p2) → p3) → p2) ∨ p2)) ∨ True) ∨ (True ∨ (p5 ∨ p4))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207945938418314602746601089026 : (((p1 → (p4 ∧ p2)) ∧ (p1 ∨ p5)) → (p3 → ((((p4 → p2) ∧ True) ∨ (p3 ∧ ((((True ∨ p2) ∧ True) ∧ p2) → (False → p2)))) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63044820874691716181748371801 : ((p5 ∧ ((((p3 ∨ (((((((p1 → (p1 → p2)) ∨ p2) ∨ p5) ∧ p3) ∨ False) ∧ p5) ∨ p3)) ∧ p2) ∧ ((p3 → p1) → p1)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205468067483897162937999709370 : (((p3 → (False → False)) → (True → p2)) ∨ ((((p2 ∧ p5) ∧ (p4 ∧ True)) ∧ ((True ∨ True) ∨ (((False → p2) ∧ (p1 → p5)) ∨ p5))) → p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309645214133566543733767261597 : (p2 ∨ (((p5 → p3) → ((p2 ∧ ((p3 → (((p2 ∧ (p3 ∧ (p5 ∨ True))) → True) ∨ (p2 ∧ p1))) ∨ p2)) ∨ p3)) ∨ ((p1 ∨ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49793723068975609054751668809 : (((p5 ∨ (((p4 ∧ p2) ∨ (((p1 ∨ p5) ∨ (p2 ∨ (p4 ∧ p1))) ∨ (p3 ∧ (p3 ∨ p3)))) ∧ (p4 ∧ p5))) → ((False ∧ p5) ∨ p5)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h5.left
      let h10 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Conjunctions on the left can always be decomposed.
            let h15 := h5.left
            let h16 := h5.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h16
          case inr h17 =>
            -- Conjunctions on the left can always be decomposed.
            let h18 := h5.left
            let h19 := h5.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h19
        case inr h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h21 =>
            -- Conjunctions on the left can always be decomposed.
            let h22 := h5.left
            let h23 := h5.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h23
          case inr h24 =>
            -- Conjunctions on the left can always be decomposed.
            let h25 := h24.left
            let h26 := h24.right
            -- Conjunctions on the left can always be decomposed.
            let h27 := h5.left
            let h28 := h5.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h28
      case inr h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- Conjunctions on the left can always be decomposed.
          let h33 := h5.left
          let h34 := h5.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h34
        case inr h35 =>
          -- Conjunctions on the left can always be decomposed.
          let h36 := h5.left
          let h37 := h5.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340948707559553893486026729742 : (p2 → (((p4 ∨ (True ∧ p2)) ∧ ((((p5 ∧ ((True ∨ p5) ∨ (p1 ∨ False))) ∧ (p5 → p2)) ∨ (False ∧ p4)) ∧ (p1 → (p2 ∧ p5)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179826554364176692307743711650 : (((p3 ∧ ((((p3 ∧ (p3 → p2)) ∧ p3) ∨ (p1 → p4)) ∨ p2)) ∧ p4) → (p1 → (((p5 ∨ p5) → ((p2 ∨ p2) ∧ (p4 ∨ False))) ∨ p3))) := by
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
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249718931628456213042387922184 : ((p5 ∨ p5) ∨ ((p3 → ((p5 ∨ ((p1 → ((p1 ∧ False) → False)) ∧ (p4 ∨ (p4 → ((True → False) ∨ False))))) ∨ (p3 ∨ (p5 ∨ p2)))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727265203442696338030097500391 : ((((p1 ∧ (False ∧ p4)) ∨ (((True → ((p5 ∨ (True ∧ p5)) ∧ p1)) ∨ ((False ∧ p2) → (((p2 ∨ False) → p4) ∧ False))) ∨ (False ∧ p2))) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646120580482103306667624012588 : ((((True → (p5 → ((((p5 ∨ p3) ∧ ((((p4 ∨ p4) ∨ p5) ∧ p3) ∧ True)) ∧ p2) ∨ (p4 ∨ (p5 ∨ (p3 → (p1 ∨ p2))))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263582071283501988158980234486 : (True ∧ ((p2 ∧ (p2 ∧ (((p5 ∨ (p3 ∨ p2)) → (((False → p3) ∨ ((True ∨ True) ∧ True)) → p1)) ∨ p1))) ∨ ((p5 ∧ False) → (True ∧ p5)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67480866016126061789272934575 : ((p1 → (((p5 ∧ p2) ∧ (True ∧ (p4 ∧ (False ∨ ((p2 ∨ (p5 ∨ p1)) ∨ True))))) ∨ ((((p3 ∧ p5) ∨ p4) ∧ False) → (p3 → p1)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213223642779710237382911475000 : ((((True ∧ p2) → False) ∧ p4) ∨ ((p1 ∨ (p1 → (((True → p4) ∨ (((p3 ∨ (p2 ∨ False)) → p2) ∨ p5)) → (p2 ∨ p1)))) ∨ (False ∧ False))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116682107053564818197987362892 : (((True ∧ False) ∨ ((p2 ∧ (((p5 → p1) ∧ (p1 ∧ (p5 ∨ (((p2 → p3) ∧ p2) → p1)))) → ((False ∧ p5) ∨ p4))) ∧ p3)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208361391306196599645211192222 : (((False ∧ p1) ∨ ((p3 ∨ p3) ∨ p3)) → (((True → (p2 → True)) → (((p2 → False) ∨ (p3 ∨ p2)) ∨ (p5 ∨ p5))) ∨ ((p4 ∨ p4) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240018541416724632728072255823 : ((p4 ∨ True) ∧ (((((p1 ∨ True) → (True ∧ (p1 ∧ False))) → (p2 ∧ p1)) ∨ (False → (p3 ∧ p1))) → ((True ∧ ((True → False) ∧ p5)) → p4))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h12 := h5 h11
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165423076981883964982395001219 : ((((p4 ∧ (p5 ∨ (False ∧ p4))) ∨ ((False ∧ p5) ∨ (True ∧ p5))) → (False ∧ (p1 ∧ p1))) ∨ (((((True → False) ∨ False) ∨ p2) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51181551849509193559638595839 : ((((p4 ∨ (((True → True) ∧ (p1 → True)) → (p4 ∨ (p1 ∨ (p3 ∨ p5))))) → (p3 ∧ True)) ∨ ((p2 → True) ∨ ((False → False) ∧ p2))) ∨ False) := by
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
theorem thm_5_vars_261314919398162744682494221757 : ((p5 → False) → ((((True ∧ (((p2 ∨ True) ∨ (p1 → False)) ∧ (p4 → (p1 ∧ (False ∨ p1))))) ∧ (True ∨ True)) ∧ (p1 ∧ (p3 ∧ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171703470664025024055011029197 : (((p3 → ((((p4 ∨ (p5 → p4)) ∧ False) ∧ ((p1 → p5) → True)) ∧ True)) ∨ p5) ∨ (True → ((p5 ∨ ((p2 ∨ p4) ∨ True)) ∨ (False → p1)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205897281804884545744260958104 : ((True ∧ (False ∧ (True → (p4 ∨ True)))) ∨ (((((p1 ∨ True) ∧ True) ∧ False) ∧ ((True ∨ (False ∧ True)) ∨ p2)) ∨ ((p5 ∧ p1) → (p3 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666021379535787808474531113573 : (((((True → ((p1 → ((((((p2 ∧ (p2 ∧ (p5 → p3))) ∨ p5) ∧ p3) → p2) → False) → False)) ∧ True)) → p3) ∧ (p1 ∨ (p3 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1449574429596549287622965220 : ((p2 → (((True ∨ p4) ∨ (p4 ∨ True)) → ((p3 ∨ (p5 → ((False ∨ p5) ∨ (p2 → (p5 → p1))))) ∨ (p3 ∧ p4)))) ∧ (p2 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
  -- Implications on the right can always be decomposed.
  intro h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187565917765866944880355103293 : ((p3 ∨ ((False ∨ (p2 → ((p4 → (True ∨ p2)) → p4))) ∧ p3)) → (p3 ∧ ((((p3 ∨ p4) ∨ (p3 → p4)) → p5) → ((p4 ∧ p5) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  -- Implications on the right can always be decomposed.
  intro h8
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55249092691269232519521509087 : ((((p3 → p4) ∧ (False → (p3 ∧ False))) ∨ (p3 ∨ ((p1 ∧ (p4 → ((p3 ∧ p3) ∨ ((p2 → p4) → p1)))) ∧ ((True → p4) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647248823066996147480444700179 : ((((p4 → ((p1 → (((p2 ∨ (p3 → (p3 → (((p1 ∧ p4) ∧ p4) ∧ p5)))) ∨ (False → (p2 → p4))) → (p2 → p5))) ∧ p5)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607466250703143655120218194210 : ((((((p4 ∧ p2) → (((((p2 → True) ∧ (p4 ∧ p3)) ∧ (p2 → (p2 ∨ ((p3 ∧ (p4 ∧ p4)) → p5)))) ∨ False) → p1)) ∧ p4) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163129160793239788509755717331 : ((((((p4 ∧ (p2 → True)) ∧ p4) → p2) ∧ (p2 ∨ p1)) ∨ (p2 ∨ ((p5 ∧ p4) → p4))) ∧ (p3 ∨ ((((p2 ∧ True) ∨ False) → p3) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157942522021530930956304384686 : (((True ∧ (p2 ∨ (p5 ∧ ((p3 ∧ p5) → p4)))) ∧ (((p1 → p1) ∧ p1) ∨ ((False ∧ p1) ∧ p1))) ∨ ((p4 → p5) → ((p2 → True) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596820178417784786379337846052 : ((((((p1 ∧ ((p2 ∧ p3) ∨ p2)) ∨ False) ∨ (True → ((False ∨ False) ∧ ((False ∧ p2) ∨ (p5 → (p3 ∧ ((p1 ∨ p3) ∨ p1))))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64867177470867061798234552711 : ((p2 ∨ (((p2 → (p3 → p3)) → (p4 ∨ ((((True ∨ (p3 ∨ p5)) → p3) → (False → False)) ∧ ((p2 ∨ True) → p4)))) ∨ (p2 → p2))) ∨ p3) := by
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
theorem thm_5_vars_316377554949541214084304267502 : (p3 ∨ (False ∨ ((((False → False) → ((p5 ∨ (p2 ∨ (p5 ∨ (p1 ∧ ((True ∨ p5) ∨ (False → (p3 ∨ p4))))))) ∧ False)) → p3) ∨ (True ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → False) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257337128922261950369603104014 : ((p2 ∨ p4) → ((p3 ∨ (p1 ∧ p1)) ∨ ((p2 ∧ (p5 ∨ (True ∧ p4))) → (((p3 → (p5 ∨ False)) ∨ (True ∨ ((p4 ∨ p1) ∧ p2))) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352094253053160667842352750803 : (p4 → (((((p1 ∧ False) ∨ False) ∧ False) ∨ p3) ∨ ((False → p1) ∨ (p3 → (p3 ∨ ((((p5 → (False ∧ p5)) ∨ p4) ∧ (p4 ∧ p4)) ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149261989304953043783324202279 : (((p4 ∨ p5) ∨ ((((p4 → (False → False)) → ((p4 ∨ (p5 ∨ p5)) ∧ p1)) ∧ (p5 → p1)) → (p1 → p4))) ∨ (((p1 → True) ∨ p5) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157910474056346919272448005657 : (((((p1 ∨ p2) → p4) ∨ ((p5 ∨ p5) ∧ (p2 ∧ p1))) → ((p5 → ((p4 → p4) → p3)) ∨ True)) ∨ (((p3 ∨ p2) ∨ (p5 → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114849809508686090296564885842 : ((((p2 → ((p3 → (p3 ∧ (p4 → (p3 ∨ p3)))) ∧ (p5 ∨ p3))) ∨ p2) ∨ ((((p3 ∨ (p1 ∧ False)) ∧ p4) ∨ p4) → p5)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248668737901455159501050365622 : ((p3 ∨ p1) ∨ (p4 ∨ (((False ∨ p1) ∧ p4) ∨ (p5 → (p2 → ((p2 ∨ False) → (((p4 ∧ p2) ∨ False) → ((False → (p5 → p1)) ∧ p2)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h5
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324648023763783972767852890585 : (p5 ∨ (((False ∨ p3) ∨ p3) ∨ (((True ∨ p1) ∨ False) → ((p1 ∨ p1) ∨ (True ∨ ((((p5 → p4) ∨ p3) → (p3 → p4)) ∨ (p4 ∧ p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651245218237640963944124815733 : ((((((p4 ∨ True) ∨ p1) ∧ (False ∨ ((p5 ∧ ((((p5 → p5) ∨ p2) ∧ ((False → (False ∨ p1)) ∨ p1)) ∧ True)) ∨ p1))) ∧ (p2 ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171574186121469179124767340941 : ((((((p4 ∧ p5) ∧ ((p2 ∨ p2) ∧ p3)) ∨ (p1 → False)) ∨ (p3 ∨ p1)) ∨ p1) ∨ (False → ((p2 ∨ p3) ∧ (False ∧ (True ∨ (p2 ∧ p3)))))) := by
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
theorem thm_5_vars_113783334489919208997047042130 : (((((False → p4) ∨ p3) → ((((True ∧ p3) ∧ True) ∧ p4) ∨ ((((p3 → p5) → False) ∨ True) → (p1 → False)))) → (p5 ∨ True)) ∨ (p4 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175121667711074053147171878398 : ((p4 ∧ (p1 ∨ ((p5 ∨ ((True ∧ True) → (True ∨ (p1 ∨ (p3 ∧ p1))))) ∧ p5))) → (((p1 → True) → (p3 ∧ p1)) ∨ (False → (False ∧ p2)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h10
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h12
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319636063310745035391580891430 : (p4 ∨ (((True ∨ ((p5 → p4) ∨ (p3 → p5))) → False) ∨ (((p5 → p5) ∨ p1) ∨ (False ∨ (False → (((p5 ∨ (True → True)) ∨ p5) → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_804267850249872275282334696321 : (((p3 → (((((p4 → (p1 → (p1 ∨ (True ∨ True)))) ∨ (p5 ∧ p2)) → p2) ∧ p5) ∨ (((False ∧ p4) ∨ (p2 ∧ (p2 ∨ p5))) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137277181558580724005973246796 : ((p1 ∧ (p3 → ((p1 ∨ False) ∨ ((((p5 → p3) ∨ ((p4 → p2) → False)) ∨ p3) → (p2 ∨ ((True ∨ True) ∧ p4)))))) ∨ (p1 → (p4 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147917546104374550169541131424 : (((((((p2 → p4) ∨ ((p3 ∧ p3) ∧ p2)) ∧ False) ∨ (False ∧ p1)) ∧ (p5 ∧ (p4 ∧ False))) ∧ (p5 ∧ p3)) ∨ (p5 ∨ ((p3 ∧ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255425703638175364087101943186 : ((p5 ∧ p1) → (((True ∧ p4) ∧ (((p3 ∧ (True ∨ p5)) → p1) → (False ∧ (p2 ∧ ((True → (p2 ∧ True)) ∧ ((True ∧ p2) ∧ p5)))))) ∨ p5)) := by
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
theorem thm_5_vars_244215009850314486210201162642 : ((True ∧ p5) ∨ (((((False ∨ p1) ∧ p2) ∧ p4) ∧ p1) ∨ ((True ∧ p1) → ((p5 ∨ p5) → (((True → (p4 → (p3 ∨ p1))) → p3) → p5))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44544249732439317849938515055 : ((((False ∨ ((p5 → (p5 ∧ ((p2 ∧ True) ∧ p5))) ∨ p5)) → (((p1 → (False ∧ (p1 → p3))) ∨ ((True ∧ False) ∨ p2)) → p3)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337108548200868534352231183475 : (p1 → ((((p3 → p3) → p4) → ((True ∨ p3) ∧ (True → ((p1 → ((p3 ∨ p3) ∧ (True ∧ ((False ∧ p5) ∨ False)))) ∨ p4)))) ∨ (p3 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748998077470422205790709248155 : ((((p4 → p4) → (False ∧ ((((((p3 ∧ ((p2 → ((p3 → True) ∧ False)) ∨ False)) ∨ p1) ∨ p4) ∨ (p5 ∨ p2)) ∧ (p4 ∧ True)) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354671144791690551610714042512 : (p5 → (((p4 ∨ ((((True ∨ ((p4 ∧ p1) ∧ p1)) ∧ (p4 ∨ ((p5 ∨ ((True → False) ∧ (p4 ∧ p5))) ∧ p2))) ∧ p5) → True)) → p2) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234924373483355136759739242962 : ((True ∧ True) ∧ ((p3 → ((True ∧ (p3 ∨ p5)) ∨ p5)) → (((False ∨ ((((False ∧ p1) ∧ True) ∨ True) ∧ (p2 ∨ p4))) ∨ True) ∧ (p1 → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117530573505872217803734112921 : ((p2 ∧ ((p5 → (((p1 ∧ p1) ∧ p1) ∧ (((p1 ∧ p1) → (False ∨ p4)) → ((False ∨ False) ∨ (p3 ∧ (p4 → p2)))))) → p5)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342392672630238203304656981382 : (p2 → (((((p2 → p3) ∨ (p1 → p3)) ∨ p2) → (((p1 → p5) ∨ p3) → (p2 ∧ False))) ∨ (((p3 → (p4 → True)) ∨ (p5 ∧ p1)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791333306913047319671919305812 : (((True → (((p3 ∨ ((p2 → ((((p1 ∨ ((p2 → p4) ∨ False)) → (p2 → True)) ∨ p2) ∧ (True ∨ p5))) ∨ (p4 ∨ False))) → p2) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137822024046894621944227187792 : ((p3 ∨ ((((p3 ∧ (p1 → (((((p2 ∨ p5) ∧ p4) → p3) ∨ p3) → ((p3 ∨ True) → p5)))) ∨ True) → p1) → False)) ∨ (p5 → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149008892748570823623252234135 : ((((p5 ∨ p5) ∧ p1) ∨ (p3 → ((((p3 ∨ p2) → p2) ∧ ((p5 ∧ p3) → (p4 ∧ (p5 ∧ p1)))) ∧ p2))) ∨ (((True ∨ p2) → p1) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692684363716194655610195367564 : ((((((p2 → ((p3 ∧ True) ∨ p3)) → p1) ∨ ((p4 → p1) ∨ (p1 → p2))) ∧ ((p1 → ((((p3 ∨ p5) ∨ True) ∧ p2) ∧ False)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248362174565511647531734462817 : ((p2 ∨ p3) ∨ (False ∨ (p4 → (True ∧ (p2 → ((p1 ∧ (p2 ∧ (False ∨ p4))) ∨ (((p4 ∧ False) ∨ (True ∧ (False ∧ (p3 → p1)))) → p1))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112275078246591857409785187824 : (((True → (((((p2 → p4) ∨ ((True → (True ∧ (p5 → p4))) ∨ p1)) ∨ ((p2 → p4) → True)) → p5) ∧ (p4 ∨ p5))) ∨ True) ∨ (p4 → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_914392284953806692014628496045 : ((((((p1 ∨ ((True → (p1 ∨ (p1 ∨ p4))) → True)) → False) ∨ (p3 ∧ (p5 ∧ True))) ∧ ((p4 ∨ (p4 ∧ p2)) ∨ ((p1 ∧ p2) ∧ p3))) → p5) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h7 : (p1 ∨ ((True → (p1 ∨ (p1 ∨ p4))) → True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h8
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h9 := h4 h7
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h13 : (p1 ∨ ((True → (p1 ∨ (p1 ∨ p4))) → True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h15 := h4 h13
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h21 : (p1 ∨ ((True → (p1 ∨ (p1 ∨ p4))) → True)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h22 := h4 h21
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- One of the premise coincides with the conclusion.
        exact h26
      case inr h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h30.left
        let h32 := h30.right
        -- One of the premise coincides with the conclusion.
        exact h26
    case inr h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h33.left
      let h35 := h33.right
      -- Conjunctions on the left can always be decomposed.
      let h36 := h34.left
      let h37 := h34.right
      -- One of the premise coincides with the conclusion.
      exact h26
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39828138916077991836270685968 : (((p1 → ((p4 ∨ (p3 ∨ ((p3 → (((p4 → (p4 ∧ p5)) → (p2 → p1)) → (p2 ∨ p3))) ∧ ((p3 ∨ False) ∧ p4)))) ∧ p2)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184041698612289406197010146832 : ((((p4 ∨ (((True ∧ p1) ∨ p1) → (False ∨ p3))) → False) ∨ p4) ∨ ((((p3 → ((p3 ∨ True) ∧ p2)) ∧ p5) → True) ∨ (False ∧ (p4 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37500963458123531215593235366 : (((((False ∨ p2) ∧ (((p1 ∧ ((False → p3) ∧ (False ∧ (p2 → ((False ∨ p1) ∨ p1))))) ∨ ((p1 → False) → p5)) → p2)) ∨ p5) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_23134764348854823971788352409 : ((((p1 ∨ (True ∨ False)) → (p5 ∧ True)) → (((p4 ∧ (((p5 ∨ p1) → (p5 ∧ (p5 → (p2 ∧ (p5 → False))))) ∨ p4)) ∨ p2) ∨ p5)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ (True ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723370949141075498534370839768 : (((((False ∧ p4) → p4) ∧ (((p3 → (((p1 ∨ p4) → ((p5 ∨ False) ∨ ((False ∧ (True → p2)) ∨ (p2 ∧ p2)))) ∨ p3)) → False) → False)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p3 → (((p1 ∨ p4) → ((p5 ∨ False) ∨ ((False ∧ (True → p2)) ∨ (p2 ∧ p2)))) ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678273535466245633030223704905 : (((((p1 ∨ ((p5 ∧ p2) → ((p2 → p4) ∧ False))) ∧ (((((True ∧ p2) ∧ p3) ∨ p4) ∨ p4) ∨ p1)) ∨ ((True ∧ p3) → (False ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702623969675558239342066174764 : (((((False → ((p1 → (p3 → p2)) ∨ (p3 → True))) → p5) ∨ ((((False → ((p4 ∧ (p4 ∧ True)) ∨ (p2 → False))) ∨ p4) ∧ p5) → p5)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346902691743116163854819295252 : (p3 → (((p3 → (p1 ∨ (((p1 → p2) → p2) ∧ ((False ∨ ((p5 ∨ p1) ∨ p4)) ∧ p2)))) → p1) ∨ ((p5 ∨ (p5 ∨ p3)) ∧ (p3 ∨ p2)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112939608077459233520798421171 : ((((p1 → p3) → ((True ∨ ((((False ∨ (p3 ∧ p1)) ∨ ((p5 ∨ p5) ∨ p5)) → ((False ∧ False) ∧ p3)) ∧ p3)) ∧ p1)) → False) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41728423032076282925459204247 : (((((False ∨ p2) ∧ (False ∨ p2)) ∧ (((False ∨ p4) → p1) ∨ ((((p2 ∨ p2) → (True ∧ p1)) ∨ (p4 ∧ p2)) ∨ (True ∧ p5)))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763466148207632163041373636507 : (((p3 ∧ (p1 ∧ ((p4 ∧ (p2 ∨ (p5 ∨ (((((p5 ∧ p4) ∨ p1) ∨ False) ∧ ((p1 → (p3 ∨ p3)) ∨ p3)) → p5)))) ∧ (p3 ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654057600034879427888740159907 : (((((True → (p4 ∨ (False ∨ (((((True → p2) → p3) ∧ (False ∨ p3)) ∧ (False → (p4 ∧ (True ∧ p4)))) → False)))) ∧ p3) ∨ (True ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164527407683328916867461211349 : ((((p5 → (False ∧ (False → (((True ∨ p3) ∧ (p4 ∧ p5)) ∨ p3)))) → (p1 ∧ p5)) ∧ p1) ∨ ((p1 ∧ p5) → ((p3 ∨ (p5 ∨ p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54006576854255996820563584766 : (((((False → (p4 ∨ (p5 → p2))) ∧ (p1 ∨ p4)) → p2) → ((p2 → p2) → ((p2 → p3) ∧ (True ∧ (p5 ∧ (p2 ∧ (p2 ∨ p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175387730216676042837047463642 : ((True → ((p4 → p1) → (((p1 ∨ p5) ∨ (p2 ∧ ((False → p1) → False))) ∧ True))) → (((p4 ∨ p1) → ((False ∧ True) ∨ (p4 ∧ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613976148157898447712222355021 : ((((((((p5 → p5) ∨ (p2 ∧ p1)) → (p4 ∧ p5)) ∧ ((True → p3) ∨ (((True ∨ p3) → p4) ∨ p2))) ∨ (p1 → (False ∧ p3))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_188432575221300380199328007127 : ((((p5 ∧ (p1 → p3)) ∨ ((p3 → p4) ∧ False)) → p5) ∧ (False ∨ ((((p4 ∨ p1) ∨ ((p2 ∨ p3) → (p2 ∨ True))) → p2) ∨ (False → p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651322619334727583284058416952 : ((((((p3 → p5) ∧ False) ∨ ((True ∨ (p2 ∨ (((p2 ∨ True) ∧ (p3 ∨ p3)) ∧ ((False ∨ p3) → (p4 → False))))) → p4)) ∧ (p2 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702990072516526362203591663855 : ((((((False → p3) ∨ p3) → ((False ∧ False) ∧ (p1 ∨ p3))) ∨ (p5 ∧ (True ∨ (((p5 ∨ (p3 → (p4 → p1))) ∨ False) ∨ (True ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617641194451343014732940271720 : (((((((True ∧ (p1 ∨ False)) ∨ p1) ∨ p2) ∨ ((False → (False ∨ ((p4 ∨ True) ∨ (((p3 ∧ p1) → (p2 ∧ False)) ∧ p4)))) → p5)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_144780676673534889246810557552 : ((((p4 ∨ p4) ∨ ((p4 → (p4 → (p4 ∧ ((True ∧ (p3 → False)) ∨ p5)))) → p1)) ∨ ((False ∧ p5) → True)) ∧ ((True ∨ p3) ∨ (True ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133611988577716474640710892038 : (((((p2 → (p1 → ((((p5 ∧ True) ∨ (p4 → p2)) → (False ∨ (p4 ∨ p2))) → False))) ∨ (p4 → p5)) → p2) ∧ p5) ∨ ((True ∧ True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65627607927734483706302488233 : ((p4 ∨ (((p5 ∨ (((((True ∧ False) → (p5 ∨ p4)) → True) ∧ (((False ∨ False) ∧ p1) → ((p2 → p5) ∨ p2))) → False)) ∨ p1) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305488816434178911431435520492 : (p1 ∨ (((False ∧ (((((True → p4) → p2) → (True ∨ p3)) → p2) ∨ p5)) ∧ p5) ∨ ((p5 ∨ p5) → ((p5 ∧ p4) ∨ (p5 ∨ (p1 ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39635569402906205284316070058 : (((p3 ∨ ((((False → ((True ∧ (p1 ∧ ((p1 ∨ p4) ∨ p2))) ∧ True)) ∨ (False ∧ (p5 ∧ (p1 → (True ∧ p1))))) ∧ p5) → p2)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52649836847166172208346992141 : (((False ∧ ((((p4 ∧ (p3 → p1)) ∨ p5) ∨ ((False ∨ p4) → True)) ∨ p5)) ∨ (((p4 → False) ∨ (p1 → p3)) ∨ (True ∧ (p1 → True)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613003693220341828588188584222 : ((((((((True ∧ (True ∨ p1)) → ((p3 → (p1 ∨ p5)) → (p5 ∧ p1))) ∨ ((p1 ∧ (False ∧ False)) → p2)) ∧ p3) → (p1 ∧ p5)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156865970674110823368097794070 : ((((((p1 ∨ (p5 ∨ (p2 ∧ True))) ∨ p4) → (p3 ∧ ((p2 → p2) → (p1 ∧ False)))) ∧ p5) ∨ True) ∨ (True ∧ ((True → False) ∨ (p2 ∨ p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164466206048724076202235126921 : ((((((((False ∨ p1) ∧ p1) ∨ p5) → (p4 ∧ (p2 ∨ (True → p2)))) ∨ p1) ∨ p3) ∧ p3) ∨ (p2 → (((p5 ∧ p3) ∧ False) → (p1 ∨ p1)))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788823021892752967259147407574 : (((p5 ∨ ((p2 → (p4 ∧ (((((p3 ∧ (p5 → p3)) ∨ True) ∨ p1) ∨ ((True ∧ p5) → p4)) → (p4 ∨ (p1 ∨ (True → p1)))))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621280911656712042767969664944 : ((((True ∧ ((((p5 ∨ (p1 ∧ p1)) ∨ (True ∨ p2)) ∨ ((p2 ∨ p1) → (p4 ∨ True))) ∧ ((p1 ∧ (p3 ∧ p4)) ∨ (False ∨ p3)))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_147701147371408359463625146037 : ((((((p4 ∧ False) → ((p2 ∧ p2) ∨ p2)) → ((True ∧ p5) ∧ p5)) → (p3 ∧ ((p2 ∨ True) ∨ p1))) → p2) ∨ (p1 → ((False → p1) ∨ p4))) := by
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



