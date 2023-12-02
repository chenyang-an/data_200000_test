variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200467976618521008906600872719 : (((p4 → False) ∨ ((True ∧ (p3 ∨ p1)) → p2)) → ((((False → p5) ∧ ((p4 ∧ (p5 → (p1 ∧ p5))) ∨ (True ∧ (p4 → p4)))) ∨ p1) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55263385611482578853705931885 : ((((True ∧ p5) → (True ∧ (False ∧ p1))) ∨ ((p5 → ((p2 ∨ p4) ∧ (p4 → (False ∨ p2)))) ∨ ((True ∨ (p2 ∧ p4)) → (False ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39413011842608300988681344524 : (((p4 ∧ (((p2 ∧ ((p4 ∧ True) ∧ p3)) ∧ False) ∧ (True ∨ (False ∨ (p2 ∨ (p3 ∨ (False ∨ (False ∨ ((p5 → p2) ∧ False))))))))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172907423246534760161435118740 : ((p2 ∧ ((p4 → (False ∧ (p5 → ((p4 → p3) ∧ False)))) ∨ (p1 ∨ (False → p4)))) ∨ ((False → p3) → ((p3 ∧ (p3 ∧ p3)) ∨ (p2 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110962729705435839272595916098 : (((((p3 ∧ (p4 ∨ p5)) → ((((p4 ∧ p3) ∨ ((p1 ∧ p5) → ((p5 ∨ p5) → False))) ∨ p4) → False)) ∨ (True ∧ p5)) ∧ True) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721984232895817896825379709927 : ((((False → ((p4 ∧ p1) ∧ True)) → ((((p3 ∨ True) → p5) ∨ (p4 ∨ (p5 → (False → ((p1 ∨ (p4 ∧ p4)) ∧ (p5 ∧ True)))))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199510205416490218093327186591 : (((p3 → (((False ∨ True) ∧ True) ∨ p4)) ∨ p1) → (((p5 → (p2 → ((False ∨ False) → p2))) ∧ ((p3 ∨ (p2 ∨ True)) → (p3 ∨ p3))) ∨ True)) := by
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
theorem thm_5_vars_690680492015652999775891499957 : (((((True ∨ ((p1 ∧ p3) ∨ (((p3 ∨ p3) ∧ False) ∨ (True ∨ (p2 → False))))) ∨ False) → (p5 ∨ (p3 ∨ (False → (p2 → (p5 ∧ p1)))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h14 =>
            -- False on the left can always be used.
            apply False.elim h13
          case inr h15 =>
            -- False on the left can always be used.
            apply False.elim h13
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h18
            -- Implications on the right can always be decomposed.
            intro h19
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- False on the left can always be used.
            apply False.elim h18
            -- False on the left can always be used.
            apply False.elim h18
          case inr h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h21
            -- Implications on the right can always be decomposed.
            intro h22
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- False on the left can always be used.
            apply False.elim h21
            -- False on the left can always be used.
            apply False.elim h21
  case inr h23 =>
    -- False on the left can always be used.
    apply False.elim h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60844889418888183544948363575 : ((True ∧ (p2 ∨ ((((p3 ∧ (True ∧ p2)) ∨ (False → (p3 ∧ p2))) ∧ (True ∧ (p4 ∨ (p3 → (False → (p5 ∨ p4)))))) ∧ (p3 ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49971107525555717228058064965 : (((((p4 ∨ p3) → ((((((p4 ∨ p4) ∨ True) ∧ False) → True) ∧ p5) ∧ True)) ∨ (p4 ∨ (p3 ∧ p2))) ∧ ((True ∨ p1) → (p4 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249989719512112425023416767348 : ((True → p2) ∨ ((p2 ∨ (False → p5)) → ((p1 ∨ (p4 ∧ (True → p2))) ∨ ((False ∧ (p2 ∨ ((p5 ∧ p5) ∧ p4))) → ((p1 ∧ p4) → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h10.left
    let h15 := h10.right
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341996748598234979010068849006 : (p2 → (((((p3 → False) ∧ p5) ∨ p5) ∨ ((p4 → (p3 ∧ ((True ∧ p1) ∧ p3))) ∧ ((p1 ∧ (p5 ∨ True)) → p3))) ∨ ((p4 ∨ p3) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318594744800596701926706977265 : (p4 ∨ ((((((p5 ∧ True) ∨ p5) ∨ (p2 ∨ (p1 ∨ p4))) → ((p1 → False) → p5)) ∨ (((p1 → (True → p1)) ∨ p1) ∨ p3)) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638052023691050976719022467338 : ((((((p1 ∨ p3) ∨ (((p3 → p2) ∨ p3) ∧ p1)) ∨ (p4 ∨ (p2 → (p1 ∧ ((p2 ∨ ((p2 → p1) ∧ (True ∧ p1))) → p4))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354195528459821807232457564307 : (p5 → (((((p2 ∨ False) ∨ p4) ∧ (False ∧ ((p2 ∧ ((p2 ∧ (p4 → (p1 ∨ ((p4 ∨ p5) → p2)))) → (p2 → p3))) ∨ p3))) ∨ p5) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199366926526729394026335739548 : ((((p5 → (p1 ∧ p2)) ∧ (p1 → p4)) ∨ p4) → ((p1 ∨ (p2 → (p2 ∨ (True ∨ False)))) → (p4 ∨ (False ∨ (False → ((True ∧ p2) ∧ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- False on the left can always be used.
      apply False.elim h7
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- False on the left can always be used.
      apply False.elim h13
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266022338549240391404932307566 : (True ∧ (p1 → (((p3 → ((p2 → ((p3 ∨ p1) ∨ p2)) ∨ p3)) ∨ False) → (True → (p4 ∨ (((p5 ∧ p5) ∨ ((p5 ∨ False) ∨ p1)) ∨ p1)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191003917065277378072372207546 : (((p1 ∧ (p3 ∨ (p1 → False))) ∨ ((p1 ∨ p1) ∨ True)) ∨ ((((True → False) → (p2 ∨ p3)) ∧ ((p2 ∨ (p2 ∨ (p5 → p5))) ∧ True)) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167854944974305004028447255515 : (((p3 ∨ (((True ∧ p5) ∨ p5) → (p3 ∨ (True ∧ p3)))) ∨ (((p4 ∨ True) ∨ p3) ∨ False)) → (((False ∧ (p1 ∨ p2)) ∨ (False → p3)) ∨ p2)) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h11
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- False on the left can always be used.
          apply False.elim h13
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186073624045054379776938103042 : ((((((False ∧ (True → True)) ∧ (p1 ∧ p1)) ∨ p3) → p5) ∨ p4) → ((((p3 → p2) ∧ ((p1 → False) → True)) → ((True ∧ p3) ∧ p4)) ∨ True)) := by
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
theorem thm_5_vars_313257737629982575788778484701 : (p3 ∨ ((True ∧ ((p3 ∨ ((p2 → p1) → (True → (p3 ∨ ((p5 ∧ (p2 → ((p4 ∧ False) ∧ p3))) ∧ (p5 ∨ (p2 ∧ p5))))))) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141736465393718274836880885081 : (((True → False) ∧ ((p5 → (True ∨ (p4 ∨ (True ∨ (p1 → (True ∧ ((p1 → p1) ∨ p3))))))) ∨ (False ∧ (False ∨ p3)))) → (p5 ∧ (p2 ∧ p4))) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h14 := h10 h13
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- False on the left can always be used.
    apply False.elim h16
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h20 =>
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h21 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h22 := h18 h21
    -- False on the left can always be used.
    apply False.elim h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- False on the left can always be used.
    apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114114796827454300341756486661 : (((p3 ∨ ((p2 → ((True ∨ p4) → p3)) ∧ ((True → ((True ∧ (p1 → (p4 → p1))) ∨ p5)) ∧ p4))) ∨ ((p3 ∧ p1) ∨ True)) ∨ (p5 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186848601486973024540300931628 : (((p5 ∧ (p2 ∨ (p2 → p3))) ∨ (p5 ∨ ((False ∨ p1) ∧ p1))) → (((((p3 ∨ p3) ∨ p4) ∨ p2) ∨ p2) ∨ (p2 → ((p3 ∨ p5) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
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
      -- Implications on the right can always be decomposed.
      intro h10
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
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338421926716972734755344994664 : (p1 → ((p4 ∧ (p3 ∨ (p3 → p5))) → (p4 ∧ ((((True ∨ (p4 ∨ (p2 ∨ (p3 → (p5 → False))))) → (False ∨ True)) → False) ∨ (p5 → True))))) := by
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
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341770120228051828146638902522 : (p2 → ((p2 → (p2 → ((((p2 ∨ ((((p4 → (p2 ∨ ((True ∨ True) → p4))) ∧ p2) ∨ p4) ∨ p3)) → p4) ∨ p5) ∨ True))) ∨ (False ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166585314378974226557176062413 : ((True → ((False ∨ ((p4 ∨ False) ∧ True)) ∧ (p5 → (p2 ∨ ((p2 → (True ∨ p2)) → True))))) ∨ (False ∨ ((False ∨ p5) → (p3 → (p5 ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254424391953491446743854538824 : ((p2 ∧ p5) → ((False → p4) ∧ (p3 → (((((False → ((p3 ∧ False) → p1)) ∨ ((False ∨ p4) → p5)) ∨ False) → ((False ∧ p3) ∧ p4)) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184671329423486715454329711756 : ((((p3 → False) → ((False ∧ p2) ∨ p2)) ∨ (p5 ∨ (p1 → p5))) ∨ (((p2 ∨ ((p4 ∨ p2) → True)) → p2) → (p4 → ((p4 → p1) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43588176828760188669840189862 : ((((((p2 ∧ ((p3 → (p4 → p3)) ∨ p4)) ∨ ((p3 → False) → ((p1 → ((p3 ∨ p3) ∨ (True ∨ p1))) → p5))) ∨ True) → p5) → p5) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∧ ((p3 → (p4 → p3)) ∨ p4)) ∨ ((p3 → False) → ((p1 → ((p3 ∨ p3) ∨ (True ∨ p1))) → p5))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231894078679055271163348515740 : (((True ∨ p5) → False) → ((p1 ∧ p4) → ((((False → (p2 ∧ (False → False))) ∧ p5) ∧ (p2 → (p2 → (((True → p5) ∨ False) → p3)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621972778724813744537261682107 : ((((p1 ∧ (p2 → ((((p3 ∨ p4) ∨ ((False → (p2 ∨ p2)) → p5)) ∧ ((False ∨ p2) ∧ p1)) ∨ ((p3 ∧ p2) ∨ (p5 ∨ True))))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_126902972628287560970735638437 : ((True ∨ (((False → ((p4 → ((p3 → p5) ∧ p2)) → p4)) → (((p5 ∨ (p4 ∧ p3)) → (p5 ∨ p2)) ∧ (False → True))) ∧ p3)) → (p2 → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117549361151516368557717838296 : ((p2 ∧ ((((p4 ∨ True) → (((True → (p2 ∨ p2)) → (p4 ∨ p3)) ∨ p1)) ∨ True) ∧ (p2 ∨ ((p1 → p1) ∧ (p1 ∨ True))))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300876545174135462818650673114 : (False ∨ (((p1 → ((True ∧ (p3 ∨ p4)) ∨ (p5 ∧ p2))) ∨ (p3 ∨ (p2 ∨ p5))) ∨ ((p4 ∧ (True ∧ p2)) → ((p4 ∨ (p5 → p2)) ∨ False)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258216213795832236149493511244 : ((p4 ∨ p5) → ((((((p2 ∨ p2) → p1) ∧ ((((True ∧ True) ∧ (((True ∨ p4) ∨ True) → p5)) ∨ (p1 → True)) ∧ p2)) ∧ p2) ∨ p5) ∨ True)) := by
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
theorem thm_5_vars_190497526395911631359467414288 : (((((p5 ∧ (p1 ∨ False)) → (False → p5)) ∨ p1) → False) ∨ ((p5 ∨ p3) ∨ ((True ∨ p2) ∨ (p5 → (((p5 ∧ (p3 ∧ p5)) ∧ p3) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53441362393920441426819612706 : ((((p2 → (True ∧ p1)) ∧ (p1 ∧ (p4 → ((True → p2) ∧ p5)))) → (((False ∨ True) ∧ (p5 ∧ (p2 → False))) → ((p3 ∧ p4) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63962126319234064638976093387 : ((False ∨ ((((p2 ∧ False) → (((p1 ∧ (p1 ∧ (p5 ∨ (True ∧ (True ∧ (p5 ∨ (p2 ∨ True))))))) ∨ (p4 ∨ p3)) ∨ p2)) ∧ p2) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148175738837985611532587990009 : (((((p3 ∨ (p2 → (False ∧ p4))) ∨ (p5 → ((p4 → p2) → (p3 ∧ p4)))) → False) ∧ (p3 ∧ (False ∨ p5))) ∨ ((False ∧ False) → (p5 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737943839069282304257068733365 : ((((True ∧ p3) ∨ (p5 ∨ (((p2 → (p5 ∧ (p2 ∧ ((p2 → p5) → True)))) ∨ (p5 ∨ (p2 ∨ (p4 → p1)))) ∨ (p5 → (p4 → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641253381100967740139637922529 : (((((p5 ∨ p1) ∨ ((p1 → (False ∧ p1)) ∧ (p2 ∨ (((p5 ∨ p5) → p2) → (p3 ∧ (((p2 → (False → True)) → p5) ∧ p3)))))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116557055876965482562525225071 : (((p1 ∨ p4) ∧ ((False ∨ p2) ∧ ((p5 ∧ ((True → (p5 ∨ p5)) → (p3 ∧ p1))) ∨ (p4 → (((False → p3) → p4) ∧ True))))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261134863203266537716583937011 : ((p4 → p4) → ((False ∧ (False ∧ ((((p2 ∨ ((p3 ∧ p4) ∧ True)) ∨ (p4 ∨ (True ∧ ((False → p1) ∨ (p2 ∨ p2))))) ∨ p5) ∨ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225976011698343999547501213485 : (((p3 ∧ p2) ∨ p4) ∨ ((p5 → ((p2 ∨ (p4 → p1)) ∨ (p3 ∧ p4))) ∨ (((p5 → p4) ∧ (p1 → True)) ∨ ((p2 → (p3 ∨ p2)) ∨ p2)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324374667848176678408883849145 : (p5 ∨ (((p3 ∨ p5) → ((p5 → p1) ∨ p2)) ∨ (((p4 → p1) → (p2 ∨ (p3 ∧ ((True ∧ p3) ∨ False)))) → (((p4 → p3) ∨ p2) ∨ True)))) := by
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
theorem thm_5_vars_179261680550801554390108207708 : ((p5 ∧ (p3 → ((((p5 → p5) ∨ (True ∨ p4)) → p2) → (p3 ∧ p5)))) ∨ (p1 → (True ∧ ((False ∨ (p1 ∧ ((False ∨ p5) → p5))) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205675700291023691681834510436 : (((p3 ∨ False) ∨ ((p1 ∧ p5) → p2)) ∨ ((p3 ∧ (p4 ∨ ((p5 → (p1 ∧ p1)) → ((p1 ∨ p4) ∨ (p5 → (p1 ∨ p2)))))) ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63321994337055686129727993499 : ((p5 ∧ ((p4 ∨ False) ∨ ((p4 ∨ (False ∧ ((p3 ∨ (((True ∨ p1) ∨ ((p3 ∨ False) → (False ∧ False))) ∨ (p4 ∧ True))) → p4))) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172120846370553343144067075590 : (((((p1 ∧ (p4 → ((p3 ∧ True) → p5))) → True) → p4) ∧ ((True ∧ p1) ∨ p3)) ∨ (((p2 ∨ ((False ∧ False) ∨ (True ∧ p3))) ∧ False) → False)) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666109650258412255382468320535 : ((((((True ∧ p3) → (p5 ∨ (p4 ∨ (((True ∨ (True ∧ p1)) ∨ p2) ∧ ((p3 → p1) ∧ p5))))) ∧ (False → p5)) ∧ ((p3 ∧ p1) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231438264610058360244415385303 : (((p2 → p1) ∨ False) → ((True → ((p3 ∨ False) ∧ ((p5 → (((p5 → (p5 ∨ False)) ∧ p4) → (True ∧ (p2 ∨ (p1 → True))))) ∧ p5))) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67372715395350044838463081014 : ((p1 → ((((((((((((p2 → p1) → p5) → (p3 ∧ False)) ∧ p2) → p3) ∨ p4) ∧ True) → True) → p5) → p5) ∨ (p1 ∨ p1)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330570505486297673992565697163 : (True → (p5 ∨ ((True → (p1 → p5)) → ((p5 ∨ (p5 → (False ∧ (p5 ∨ p2)))) → ((False ∧ (((p1 ∨ True) → (p4 ∨ p2)) ∨ p5)) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135906910576555292596947634077 : (((((((p1 → False) → p4) → True) ∧ (False → True)) → (p5 ∧ p4)) → (((p2 ∧ p5) ∨ p5) → (False ∧ (p1 ∨ p5)))) ∨ (True → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336231864678913850435250974486 : (p1 → (((((p3 ∨ ((True → ((False ∧ p1) ∨ (p1 ∧ p4))) ∨ p1)) ∨ p1) → (p1 ∧ (p5 ∧ (p5 ∧ p4)))) → ((p3 ∧ p2) → False)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134052499725588682941384834517 : ((((False ∨ (((p4 ∨ ((True ∧ (p1 ∧ True)) ∨ (p2 ∧ p2))) ∧ ((p3 ∧ (p1 ∧ p3)) → p3)) → False)) ∨ p2) ∨ p1) ∨ ((False ∧ False) → False)) := by
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
theorem thm_5_vars_168583346277897752165454005348 : ((p2 ∧ (((p3 ∨ False) ∨ (p5 ∧ p3)) ∨ (p3 → ((((p1 ∨ True) ∨ True) ∧ False) ∧ p4)))) → ((p4 → (p5 ∧ p3)) ∨ ((p3 ∧ p5) ∨ True))) := by
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
        -- False on the left can always be used.
        apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45759535860703063845638836392 : (((False → ((p4 ∨ (p4 → (p1 ∧ p3))) ∧ (((p2 ∨ (True ∧ ((p3 ∧ p5) → p5))) ∨ (((p1 ∨ p3) → p3) ∧ False)) ∨ p4))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56544293851666229977187190263 : (((p2 ∨ ((p4 ∧ p2) ∨ p2)) → ((((p4 → p2) → (((p4 ∨ True) ∧ (p4 ∨ False)) ∨ False)) ∨ ((p4 ∨ p3) → (p4 → p1))) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801093064793826800884745440850 : (((p2 → ((p1 ∨ ((((p2 ∨ (p4 → p4)) ∨ True) ∨ (False ∨ ((p4 ∨ (p4 → False)) ∧ (p2 ∧ p4)))) ∨ p4)) → ((p2 → p1) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42746745733961201627983120813 : (((True → (((p2 ∧ p3) → p5) → (((p3 ∨ False) ∧ (p5 → True)) ∨ ((p5 → ((p3 ∧ (p2 ∨ True)) → (p2 ∨ p1))) → p1)))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_443833393603283707183995371208 : (((((True ∧ (p1 → False)) ∨ ((p4 ∧ (((p1 ∧ False) ∨ (False → p2)) → p1)) ∧ (True ∧ (False → (p1 → p2))))) ∨ (p4 → (p3 ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336399155926215328263137223867 : (p1 → ((p3 ∧ (False ∧ ((p5 → (p3 ∧ (((p2 ∨ p4) ∧ (((p5 ∧ (False → p2)) → (p1 → p5)) ∨ p4)) ∧ p5))) ∨ (p5 ∨ p1)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150555828450909141191472537483 : ((((((False ∨ p2) ∧ p1) ∨ p5) ∨ ((p3 ∧ (p5 → (p3 ∨ (p4 ∨ (True → False))))) ∧ (p1 ∧ p1))) ∧ p3) → (True → ((p2 ∧ False) ∨ p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h14.left
    let h18 := h14.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621652340431635391530944833940 : ((((False ∧ (p4 ∧ ((((p3 ∧ (True → p1)) → (p1 ∨ (((True ∨ ((p4 ∧ p1) ∧ p2)) → p3) ∧ (p1 ∨ p3)))) ∨ p1) → p1))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_118812845300705127994151588016 : ((True → (((p4 → (((p2 → p3) → (p2 ∨ (p3 ∨ p1))) ∨ True)) ∧ (p1 → ((((False ∧ p4) → p3) ∨ p5) ∨ p5))) ∨ p4)) ∨ (p2 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346365948330166436220335993259 : (p3 → ((True ∧ ((p3 → True) ∧ ((p5 ∧ p3) ∨ ((False ∨ (p5 → (p2 ∧ p3))) ∨ ((((p1 → p5) ∧ p1) ∨ p3) ∧ p1))))) ∨ (p3 ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_471410534370260249144556194095 : (((((p2 ∧ (((p2 ∧ (p2 → (p4 ∨ p4))) ∨ p5) ∧ p4)) ∧ p5) ∨ ((p4 ∨ p3) ∨ (((p2 ∧ False) → p4) ∨ (False ∧ (p2 ∧ True))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226754297409938054517400417306 : (((p2 ∧ p1) → False) ∨ ((False ∧ (((p4 → (((True ∧ True) ∨ p2) → p5)) ∨ (((p4 ∨ p4) ∧ p2) ∨ p5)) ∨ True)) ∨ ((p3 ∨ True) ∨ p3))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741146371944295831129861455420 : ((((p4 ∨ p1) ∨ ((p3 ∧ (p3 → (((p5 ∧ False) → (p1 ∨ (p1 ∧ ((p1 ∧ False) → (p4 ∨ p2))))) ∧ ((p1 ∨ False) ∧ p3)))) → p1)) ∨ False) ∧ True) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142747298335034810776718533671 : ((p2 ∨ ((p4 → p4) ∨ ((p1 → (p3 → p1)) → (((p5 ∨ ((p3 ∧ p4) ∧ p5)) → (p1 → p5)) ∧ (p3 → True))))) → (p1 ∨ (p3 ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
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
theorem thm_5_vars_62984906261746309215881076795 : ((p4 ∧ (p4 ∨ (p3 ∨ ((p3 ∧ ((((((True → True) → p1) → ((p1 ∧ p1) → ((p2 ∧ p2) ∨ False))) → p5) ∧ p2) ∧ False)) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308749116626339524383017140574 : (p2 ∨ ((p5 → (((False → (True → (p1 → (False ∧ (p1 → (True ∨ p3)))))) → (True ∨ (p2 ∨ p4))) → (((p3 → False) → p3) ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259994353734464932230832715363 : ((p2 → True) → ((p2 ∧ (((p2 → (False ∨ (((p5 ∨ ((True ∨ p2) ∨ (p3 ∨ p2))) ∧ p2) ∨ p1))) → p2) ∨ False)) ∨ (p3 → (p2 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247877118851291385452071426242 : ((p1 ∨ p2) ∨ (p1 ∨ (p2 → (True ∧ (((p3 ∨ (p2 ∧ ((((p4 ∨ p5) ∨ (p4 ∧ (p2 ∨ True))) ∨ True) ∨ False))) ∨ (p5 → True)) ∨ p2))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233451209670968218164529316226 : ((False ∨ (p2 → False)) → ((((p3 ∨ p1) → (p1 ∨ (p1 ∧ (False ∧ (((p5 ∨ (p2 ∧ (p2 → True))) ∧ (p1 ∨ p2)) ∨ False))))) ∨ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200027804223164678485590101185 : (((True ∧ ((p5 → p5) ∧ p5)) → (False → p3)) → ((((p1 → p5) ∧ p2) → (p4 → (p2 → p5))) ∨ ((False ∧ ((p2 → p4) ∧ p2)) → p4))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207930630699958447171500689396 : (((p3 ∨ (True ∨ p1)) ∧ (True ∧ p2)) → (((p5 ∨ p2) ∧ (p1 ∧ (p4 ∧ False))) ∨ ((p5 ∧ False) → (p2 → (p4 ∨ (p4 → (p5 → p1))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h3.left
      let h14 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h3.left
      let h21 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- Implications on the right can always be decomposed.
      intro h23
      -- Conjunctions on the left can always be decomposed.
      let h24 := h22.left
      let h25 := h22.right
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301745748971010325442342315957 : (False ∨ ((p2 → True) ∧ (p1 ∨ ((p4 ∧ p2) ∨ (p4 → (((((True ∨ p1) → p4) ∨ (p5 → True)) ∨ True) → (True ∧ ((p1 → False) ∨ p4)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39907620264867207347632458608 : (((p3 → ((((((p2 ∨ ((True → p2) ∧ (p5 → (((p2 → False) ∨ p5) ∨ p3)))) ∧ p1) ∧ (p1 ∨ p4)) ∧ p3) ∨ p5) ∨ p4)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612219517527325164604735314244 : ((((((p2 → ((p3 ∨ p4) ∧ True)) → ((p4 → (False ∨ ((p2 ∧ p4) ∧ ((p5 ∨ (False ∧ p2)) → p5)))) ∨ p3)) ∧ (p2 ∨ p3)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253129163345415559983974054742 : ((True ∧ p5) → ((((p2 → False) → ((p2 ∨ ((p3 ∨ p3) ∧ p3)) → ((p2 ∨ ((p1 ∧ p2) ∨ (p1 → p1))) ∨ p5))) → p1) → (p1 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : ((p2 → False) → ((p2 ∨ ((p3 ∨ p3) ∧ p3)) → ((p2 ∨ ((p1 ∧ p2) ∨ (p1 → p1))) ∨ p5))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h14 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h1.left
  let h16 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89342485949842920190144236413 : (((p4 ∨ (p3 ∨ p1)) ∧ ((p4 → ((p2 → p4) ∧ (((p5 → p5) → (((p3 ∧ (p5 → False)) ∧ (p2 → p3)) ∨ p3)) ∨ p4))) → p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (p4 → ((p2 → p4) ∧ (((p5 → p5) → (((p3 ∧ (p5 → False)) ∧ (p2 → p3)) ∨ p3)) ∨ p4))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h5
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : (p4 → ((p2 → p4) ∧ (((p5 → p5) → (((p3 ∧ (p5 → False)) ∧ (p2 → p3)) ∨ p3)) ∨ p4))) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h13
        -- One of the premise coincides with the conclusion.
        exact h12
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h14 := h3 h11
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601761517652962506607688193581 : ((((p4 ∧ ((((p4 → (True ∧ (True → ((p1 ∨ ((p1 ∨ False) ∨ (True → p1))) ∨ True)))) ∨ ((True ∧ p5) ∨ False)) ∨ p1) → False)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51639564157488469530594921842 : (((((p1 → ((((p5 ∧ p1) ∧ p5) ∨ p5) ∧ p3)) ∨ (p4 ∧ (p2 ∨ p2))) ∨ p3) ∧ ((True ∨ (p3 ∧ p3)) → (p5 → (p4 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117340940692377244917276282942 : ((False ∧ ((p4 ∧ True) ∨ ((True → ((p2 ∧ (True ∨ p5)) → ((p4 ∨ (p2 ∧ ((False ∧ p2) ∧ p4))) ∨ p2))) ∧ (p5 → False)))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184467793503697385348235710541 : ((((((p5 ∧ True) ∧ False) ∨ (p4 ∨ p1)) ∧ p3) ∨ (False ∨ p1)) ∨ (((p1 ∧ False) ∧ ((((True → p2) ∨ True) ∧ p5) ∨ (p4 ∨ p3))) → False)) := by
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
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305977869892112300766314402832 : (p1 ∨ ((p2 → (p5 ∨ (p5 ∨ True))) ∧ (((p4 ∨ (p2 ∧ ((p3 ∨ p5) → (True → (p4 → (p2 → (p3 → False))))))) ∧ (p3 ∧ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172603326574299276475205109017 : (((True ∨ (p3 → True)) → (p3 ∨ (((False ∨ p5) → (p1 → p4)) ∨ (p2 ∧ True)))) ∨ ((p1 ∨ (p4 ∧ (p5 ∨ ((p5 → False) ∧ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217618981332149655569624639402 : ((((p5 → p5) ∨ True) → p5) → ((True ∧ (((False → ((p3 ∨ p1) → False)) → p2) ∨ (p3 → ((p2 ∧ p1) ∨ ((p1 ∧ p5) → p4))))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 → p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169045481398734032916235099463 : ((p2 → (p4 ∧ ((((p2 ∨ True) → (False → p5)) → ((p5 → p4) ∧ (p5 ∨ p1))) → p1))) → (False ∨ (p5 ∨ (p3 ∨ ((False → p3) ∨ p5))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48363610781337850308973870690 : (((p4 ∨ (p4 ∨ (True → (((False → (p3 ∨ p1)) ∨ p4) → (((p3 ∨ p3) ∧ (p4 → (p3 ∧ (True → False)))) ∨ p1))))) → (p4 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224897466413199557415661317717 : ((p5 → (True ∨ p5)) ∧ (p4 ∨ ((p2 → p1) ∨ ((p2 → (p1 → ((p5 → p4) ∧ ((p2 ∧ p1) ∧ (p2 ∧ p4))))) ∨ ((True → True) ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_190674909952553707541314375702 : (((p2 → ((p1 ∨ False) ∨ (True → (True → p4)))) → p1) ∨ ((p5 ∨ True) ∨ (p3 ∧ (p3 ∧ (((((p1 ∨ True) → False) ∧ False) ∨ p5) ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227290957724510358437460107875 : (((p1 → p5) → p3) ∨ ((False ∧ ((p1 ∧ (p1 → ((((p3 → p3) ∧ p3) ∨ False) ∨ p1))) → p4)) ∨ (((p4 ∧ p3) ∨ (p4 ∧ p3)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205915542466664064506525221980 : ((False ∧ (((p2 ∧ p3) ∨ False) ∧ False)) ∨ ((p1 ∨ (p2 ∧ (((p3 → p3) ∧ p1) ∧ True))) → (((p4 ∧ (p2 ∧ p5)) ∨ (p2 ∨ False)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314419194388078771443119723580 : (p3 ∨ (((p1 ∨ ((p2 → (p4 ∧ (p3 → True))) → (p2 ∨ ((p4 → p4) ∨ p1)))) → ((p5 ∧ p2) ∨ True)) ∨ ((p1 ∨ (p1 ∨ p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179424397389286575684644320710 : ((p4 ∨ ((True ∨ (p1 ∧ (False ∨ False))) → (((p4 → p3) → p5) ∧ p4))) ∨ (p3 → ((p1 ∨ ((True ∨ False) ∨ p3)) ∨ ((p5 ∨ p5) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702217652773079324835779028469 : ((((((p5 ∧ ((True → p2) → (p3 → False))) → p3) ∧ True) ∨ (p3 → (p1 ∧ (((p5 ∨ p1) ∧ (True ∧ False)) ∧ ((p5 ∧ p4) ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



