variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36155122191992066536830305665 : ((p3 → (p5 ∨ (p3 ∧ ((p5 ∧ p5) → (((p4 ∨ False) ∨ (p1 ∨ p5)) ∧ (((False ∧ False) ∨ p5) ∧ ((p5 ∧ False) → (p4 ∨ p2)))))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153419927044334576500227777275 : ((p3 ∨ (True → (True → (((False ∧ ((((p2 → p4) ∨ (False ∨ p3)) ∨ (p5 → False)) ∨ p5)) ∧ p4) → p5)))) → ((p4 ∧ (p2 ∧ p1)) → p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47511648341736446130230613473 : (((p2 ∨ ((p5 → (p2 ∧ (p3 ∧ True))) → (((((p1 ∨ p5) → p2) ∨ (((False ∧ True) ∧ p4) ∨ p4)) ∧ True) → p5))) ∨ (p5 → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666127186093910956480746035600 : (((((p4 ∨ ((True → (False ∧ p5)) ∨ (((p3 ∨ p2) ∨ (p2 ∧ p5)) ∧ ((p4 ∨ p2) ∨ p4)))) ∧ (p1 → p2)) ∧ (p2 → (p1 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41056076971020939707029567790 : (((((p1 ∧ p1) → (((p2 ∧ p5) ∧ p3) ∧ ((p4 ∨ p1) → ((p4 ∧ (True ∧ (p4 ∨ (True → p4)))) ∧ True)))) → (p2 → p2)) ∨ p2) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326839225960682814820184783683 : (True → ((((p4 → ((p4 ∨ p1) ∧ ((p2 ∧ (p1 → p1)) → False))) ∨ ((True → ((p3 ∧ (False ∨ p1)) ∧ p3)) ∨ (p3 → p5))) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117397493335639661314232392551 : ((p1 ∧ (((p5 ∨ (p3 ∨ False)) → ((((((True ∨ p5) → False) → ((False ∨ False) ∧ False)) ∨ p5) ∧ (p4 ∨ p5)) → p5)) ∨ p5)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54205996091610909921620777910 : ((((False ∧ (True ∧ ((p5 ∨ p2) → False))) ∨ p1) ∧ (p2 ∧ ((((False → p3) → (((p2 → p5) ∨ True) → False)) → (p5 ∧ False)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134143662179588559467211178473 : ((((((p1 ∨ (False ∧ (p1 ∨ (p5 ∨ (p4 ∧ (True ∨ p5)))))) → False) → (p2 ∧ p2)) ∧ ((p4 → p4) → True)) ∨ p5) ∨ ((p4 ∧ False) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341066345256126630450866769335 : (p2 → ((p4 ∨ ((((p1 ∧ p3) ∨ p2) → p5) → ((((p5 → p2) → (p1 ∨ True)) ∨ True) → (False ∨ ((p1 → (p3 ∨ p4)) → p5))))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230962569837102380510279563395 : (((p4 ∧ False) ∨ p3) → (((((p5 → (False ∧ p2)) ∨ p4) ∨ ((p1 ∨ (((False ∧ ((True ∧ False) ∨ p5)) → p4) ∨ p2)) ∧ p1)) ∧ p1) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59406146575708048670919763496 : (((True → p4) ∨ (((p4 ∧ ((p3 → ((p1 ∨ p1) → ((((p3 ∧ p1) → (False → False)) → p4) ∧ p2))) → False)) ∨ (p4 ∧ p1)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18028861482348502705870998950 : ((((p5 ∨ p4) ∨ ((((p2 ∨ p1) ∨ False) ∨ ((p4 ∨ (p3 → p3)) ∧ (p3 → p2))) ∨ (p4 ∧ p3))) ∨ (True ∨ (p1 ∧ (p1 → p2)))) ∧ True) := by
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
theorem thm_5_vars_172624324129214769776507295984 : (((p1 ∧ p5) ∧ (True ∧ (((p1 ∧ ((True ∧ p3) ∨ False)) ∨ (p4 → True)) ∧ False))) ∨ (((False → ((p1 ∨ p1) ∨ p2)) ∧ (True ∨ False)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116545060070401722712583473552 : (((False ∨ p4) ∧ ((((p1 ∧ p2) ∨ (((False ∨ p3) → (p5 ∨ (p1 ∧ (p2 ∨ p4)))) ∧ (False → False))) ∧ (p2 ∧ p2)) ∧ False)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40532249897187390521242885848 : ((((p1 ∨ (p4 → ((((p2 → (p1 ∧ ((p2 ∧ (True ∧ True)) → (p1 ∧ p2)))) ∨ p1) ∨ p3) ∧ ((p2 ∨ p3) ∧ p4)))) ∨ True) ∨ p1) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626769933603854258406083103950 : ((((p5 → ((((p2 → ((p1 ∧ p1) ∧ True)) ∧ ((((p5 → False) ∧ (p1 ∨ p2)) ∨ p4) → p2)) → p2) ∧ ((p4 ∨ p5) ∧ p4))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_336372325860486684487584823278 : (p1 → (((p5 → p3) → ((((((False ∧ False) ∧ (p4 ∧ False)) → True) → p2) ∧ p1) ∨ (True ∧ ((p4 ∨ p1) ∨ (p2 → (True ∨ p3)))))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64011567676949564975202699106 : ((False ∨ ((((((p3 → p1) → p3) → False) ∧ ((p5 ∨ (p4 → p2)) → (p4 ∧ (p3 ∧ ((p1 ∧ p1) ∨ True))))) ∨ p1) ∨ (True ∨ p4))) ∨ p5) := by
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
theorem thm_5_vars_197981599443078170678512368047 : (((p2 ∨ p3) ∧ ((False ∨ (p2 ∨ p3)) ∨ True)) ∨ (False → ((p5 ∧ (p2 → (p1 → ((p2 ∨ p2) → (p2 ∨ p1))))) ∨ (p1 ∨ (False ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613600279902796113838545764864 : (((((((p4 → p2) → (True → (p4 ∧ (((True ∨ p5) ∧ p4) → ((p1 → (p2 ∧ p5)) ∧ p2))))) → False) ∧ ((False → p3) → p5)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721817852633167375837289721561 : ((((p3 ∨ ((True ∨ p2) ∨ p4)) → ((True ∧ ((((True ∧ p1) ∨ (p4 ∨ ((p3 ∧ (p1 ∧ p3)) ∧ False))) ∨ p1) ∨ (p3 ∧ p4))) ∨ True)) ∨ p4) ∧ True) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
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
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42841224620945743362156764048 : (((p2 → ((((((p1 → (p2 ∧ p1)) ∧ p4) ∨ (((((p1 ∧ True) → p5) ∨ True) ∧ p3) → True)) ∧ p4) → (p1 ∨ p3)) ∧ p1)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807031010833214747893959871953 : (((p4 → ((((p2 ∨ ((p2 ∨ p5) ∧ p3)) ∨ p1) ∨ ((p5 → p2) ∨ ((p1 ∨ p2) ∨ ((False ∨ p4) ∨ False)))) → (p5 ∨ (p3 ∨ p4)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- False on the left can always be used.
            apply False.elim h20
          case inr h21 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
        case inr h22 =>
          -- False on the left can always be used.
          apply False.elim h22
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748899810879256414750136455446 : ((((p4 → p2) → (((p2 → (p4 ∧ ((p5 ∧ p2) ∧ p1))) → (p1 → (((p5 ∨ True) → p3) → (p5 ∨ (p3 ∨ (False → p4)))))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730064761991928230003629209353 : (((((p2 ∨ True) → p4) → ((p4 ∧ (p4 → False)) ∧ ((True → True) ∧ (False ∨ (((True → p5) ∨ p3) ∨ (p3 ∨ (p5 ∨ (False ∨ p1)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172684885912258998349628724580 : (((p1 ∧ True) ∨ (p5 → (((((True ∧ True) → p5) → p2) ∧ (p2 ∧ True)) ∧ p4))) ∨ (((((p3 ∧ False) ∧ (p3 → p1)) ∨ p5) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715216295601578124319875964810 : ((((False → (True → ((True ∧ p2) ∨ p5))) → ((p4 ∧ ((True ∨ (p5 ∨ True)) → (((p3 ∧ p4) ∧ ((p1 ∨ p2) ∨ p4)) ∨ p5))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172154835363782332809836489204 : ((((((p5 ∨ ((p5 → False) → p2)) ∨ False) ∨ p3) ∨ p2) ∨ ((False ∨ True) ∨ p2)) ∨ ((p2 ∧ (False ∧ (p3 ∧ ((p2 ∨ p2) → True)))) ∨ p5)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_915054518258260516457935417888 : ((((False ∨ ((((((p2 ∨ (p3 ∧ p2)) ∧ p2) ∨ True) → True) → p3) ∧ (p4 → p3))) ∧ (p3 → (p4 ∧ (p4 → (p2 → (p2 ∧ p3)))))) → p4) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : ((((p2 ∨ (p3 ∧ p2)) ∧ p2) ∨ True) → True) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h8
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- One of the premise coincides with the conclusion.
    exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192870695772638036480074045791 : ((((p4 → True) ∧ ((p5 → p5) ∨ p1)) ∧ (p5 ∧ p2)) → (p3 → (((p4 → ((False ∨ (p1 ∧ p1)) ∧ p5)) ∨ (p3 ∨ (p2 → p5))) ∨ p2))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h4.left
    let h9 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h4.left
    let h12 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114410736056111148123961839416 : ((((p2 ∨ (p1 ∨ p1)) ∧ (((p1 ∧ ((((p5 ∧ False) ∧ True) ∧ p2) ∧ p5)) → p5) → True)) ∨ ((p5 ∨ (p4 ∧ p5)) ∨ True)) ∨ (p1 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252798440305165171468334878013 : ((True ∧ True) → (p4 ∨ ((p2 → p5) → (((p5 ∧ ((((p4 ∨ p2) → (p1 ∧ p5)) ∨ p1) → p4)) ∨ ((p4 → p5) ∨ p2)) → (p4 → p5))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h15 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h16 := h4 h15
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62347467824564136742767042125 : ((p3 ∧ ((((True ∧ p4) ∨ (p4 ∨ p5)) ∧ (True ∧ (((False ∨ p3) ∧ ((p3 ∨ (p5 → p1)) → p4)) ∨ False))) → ((p2 ∧ False) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43863380883171489808982576021 : (((((((p4 ∧ ((p1 ∨ True) ∨ True)) ∨ True) ∨ p2) ∨ ((p1 → p3) → (False ∨ (p5 ∨ ((p1 → True) ∧ p3))))) ∧ (p1 ∧ p3)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116234706593013618452742293750 : ((((p2 ∧ p3) → p1) ∨ ((True → p5) ∨ (((p2 → p2) ∧ (False ∧ (p5 → ((p2 ∨ ((False → p3) ∧ p1)) ∨ p2)))) ∨ True))) ∨ (p5 ∨ p5)) := by
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
theorem thm_5_vars_38326989402112344315385237395 : ((((p3 → (((p2 ∨ ((p5 ∧ False) → ((p2 ∧ p1) ∧ ((False ∧ p3) ∧ p5)))) ∨ p4) ∨ p4)) → ((True ∨ (False → p3)) ∧ p2)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66633882530762715853766197599 : ((True → (((p2 → False) ∧ ((p5 → (p4 → p5)) → ((p2 ∧ (p4 → p5)) ∨ p5))) → ((p1 → (p1 ∧ ((p3 ∨ p3) ∧ p4))) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693727329049135045079072156919 : (((((p1 ∨ (((True ∧ ((p3 → False) ∧ (p3 ∨ p4))) → p1) ∧ p5)) ∨ True) ∨ (((p1 ∨ (False ∨ (False ∧ True))) → (False ∧ p1)) → p5)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_752326576789385678032373899758 : (((False ∧ (((((p3 ∨ p4) → (False ∨ ((p5 → ((True ∨ True) ∨ ((p1 → True) ∧ ((p1 ∧ p3) ∧ p4)))) ∧ p4))) ∧ p5) ∨ False) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140436363423603290810671638421 : (((((p2 ∨ False) ∨ ((p2 ∧ (p1 ∧ p1)) → True)) ∨ (p3 ∧ ((p1 → (False ∨ p2)) ∧ False))) → (False ∧ (p3 ∧ p2))) → ((p2 ∧ p3) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∨ False) ∨ ((p2 ∧ (p1 ∧ p1)) → True)) ∨ (p3 ∧ ((p1 → (False ∨ p2)) ∧ False))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (((p2 ∨ False) ∨ ((p2 ∧ (p1 ∧ p1)) → True)) ∨ (p3 ∧ ((p1 → (False ∨ p2)) ∧ False))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : (((p2 ∨ False) ∨ ((p2 ∧ (p1 ∧ p1)) → True)) ∨ (p3 ∧ ((p1 → (False ∨ p2)) ∧ False))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h10
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158932626472540456335153899307 : ((p2 ∨ ((((((((p2 ∧ True) → p3) ∨ p2) ∧ False) → p3) ∧ True) → ((p3 ∧ p1) ∧ p4)) ∨ p4)) ∨ ((p1 ∨ ((False ∧ True) → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112313695457179048396081028161 : (((p2 → (p4 ∧ ((p5 → (p2 ∨ p3)) ∧ ((p5 ∧ ((p1 ∧ (p2 ∨ p3)) ∧ (((p2 ∧ True) → p2) ∧ False))) ∨ p1)))) ∨ True) ∨ (p2 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169122998410517931808964406691 : ((p5 → ((True ∧ ((p4 ∨ p3) → ((p2 → (p5 ∨ (p3 → p5))) → (p2 ∨ False)))) ∨ True)) → (True ∧ ((p4 → ((p5 → False) ∨ True)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197424632898549880803578768356 : (((p4 → (p4 ∨ ((p4 → p3) ∧ p2))) → p2) ∨ (False ∨ (((True → (p1 ∨ (p3 ∨ True))) ∨ (True ∨ p5)) ∨ (((p3 ∧ p1) ∧ p3) → p4)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249475715251834307201589657731 : ((p5 ∨ p1) ∨ ((True → ((((True → (p3 → (p1 ∨ (((True → p2) ∨ False) ∨ p4)))) → p5) ∨ p1) ∨ (((True ∨ False) ∧ p2) → True))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_256455183414464014515055821195 : ((False ∨ p4) → ((((p5 ∧ (((False → p5) ∧ ((p1 → True) ∨ p1)) → (((p3 → p3) → (p3 ∧ True)) ∨ False))) ∧ (p3 ∧ p1)) ∨ p1) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356358570437859461544711936216 : (p5 → (((p1 ∧ p5) ∧ ((p4 ∨ (p5 → (p3 → p1))) ∧ (False ∧ (True ∨ p5)))) ∨ (p3 ∨ (True ∨ ((((False ∧ p2) ∨ p1) ∨ p1) → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233799099253144480035290506504 : ((p3 ∨ (p1 → True)) → ((p2 → (((p1 → p1) ∧ p3) ∧ ((True ∨ (((p1 ∨ p2) ∨ p2) ∧ True)) → (p5 → ((p2 → p4) → p1))))) ∨ True)) := by
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
theorem thm_5_vars_213350146720617434803855963672 : (((p3 ∧ (p5 ∨ p1)) ∧ True) ∨ ((((p1 → False) → (p3 → (p4 ∧ ((((False → p4) ∧ p4) → False) ∧ (p4 ∧ True))))) → p5) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206904821840304098003113200429 : (((((False → True) ∨ p1) ∨ True) ∧ p3) → ((False → (True → p2)) → (((p5 ∧ p2) → p5) → ((p4 → ((p1 ∨ p1) ∨ p5)) ∨ (p2 → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731441332440491285711647168039 : ((((True → (p3 ∧ p2)) → ((False ∨ ((False ∨ (p4 → (p1 ∨ p1))) ∨ p4)) ∨ ((((p3 ∧ True) → (p4 ∧ p3)) → True) ∨ (p5 ∨ True)))) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_457728142578182131828961724922 : (((((((False → p5) → p1) ∧ ((p4 ∨ (True ∧ p5)) ∨ (p1 ∧ False))) ∧ (p3 ∧ (p4 → False))) ∨ (p1 → ((p1 ∨ True) ∨ (p1 ∧ p3)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148346035066555727551243572913 : (((((False ∨ (p4 ∧ True)) → p4) → (((p5 → (p3 ∨ p2)) ∨ p4) → p4)) ∧ ((True ∨ p2) ∨ (True → p2))) ∨ (((p2 ∧ p2) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110729000679119248897572994484 : (((((True ∧ (p4 → ((((p3 ∨ p4) ∧ p5) ∧ ((p5 ∧ p4) ∨ p1)) ∧ False))) ∨ ((p1 ∨ p3) ∨ (False → False))) ∧ True) ∧ True) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59256888640924673613939071803 : (((p2 ∨ p5) ∨ ((p4 ∨ (((True ∨ ((True ∨ True) ∧ False)) ∧ (p1 ∧ p2)) → False)) → ((((False ∧ p5) ∧ False) ∨ (p3 ∨ False)) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178153341324071164807560896965 : (((((p4 ∨ p4) → p1) → (False → (p5 ∨ ((p2 ∧ p4) ∨ p1)))) → p5) ∨ (p1 ∨ (p2 → (False → (p2 ∨ (False ∨ ((p3 ∨ p3) → p5))))))) := by
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
theorem thm_5_vars_259331394687447452734297855542 : ((False → p2) → ((((False ∨ ((p1 ∨ p1) ∧ (True ∧ (True ∨ (p4 ∧ p2))))) ∨ p2) ∨ p5) ∨ (((p4 ∨ p2) → p2) ∨ (p4 ∨ (False → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185017707271537376236775707023 : (((p2 ∨ False) ∧ (False ∨ (p5 ∧ (p2 ∧ (False → (True ∨ p3)))))) ∨ ((((p3 → (False ∧ p1)) ∨ p4) ∨ (((False → p1) → p2) ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135917040504387631770198443657 : ((((p5 ∧ p1) ∨ ((p4 ∧ (True → (p1 → p2))) → (p1 ∨ p1))) → ((p1 → ((p2 ∧ (True → p2)) → True)) → p3)) ∨ ((False → p1) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164796759240822880493778211837 : (((((p1 ∨ p1) ∨ True) ∧ ((p5 ∨ (((False ∧ (p3 ∧ p4)) ∨ True) ∧ False)) ∨ p5)) ∨ p4) ∨ (False → (((True → False) → p1) → (p2 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249152922966962758551343288326 : ((p4 ∨ p2) ∨ (p2 ∨ (((p4 ∧ (p3 → (p5 ∧ p5))) ∧ p2) → (p4 → ((p1 → False) → (p1 ∨ ((p5 → p1) ∨ ((p4 ∨ p1) ∧ True)))))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57885209257955821402381147791 : (((p2 ∨ (p3 ∨ p5)) → (((p3 ∨ (False ∧ ((p4 ∧ ((True ∨ (p4 ∨ (p5 ∨ p2))) → p5)) → False))) ∨ p1) ∧ (False → (p1 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37831756581314844625338858703 : ((((p1 ∨ (p5 ∨ (p3 ∨ (p2 → ((False → (p5 → ((((p2 ∨ (True ∧ p4)) → (p4 → True)) ∧ p1) ∧ p2))) ∨ p4))))) → False) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342683310486172483697336197241 : (p2 → ((((p1 ∨ ((p1 → p1) ∧ p3)) ∨ (p2 ∧ False)) ∨ False) → (((((p3 → (True → p5)) ∨ p3) ∧ p4) ∨ ((p2 → p3) ∧ False)) ∨ True))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
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
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61059979986177999474533072838 : ((False ∧ ((((p1 ∧ True) ∧ p1) ∨ ((((True → (p5 ∨ p2)) → ((False → (p2 ∨ p1)) → True)) → p2) → p1)) ∧ ((False ∧ p4) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65425890484724944379038192567 : ((p3 ∨ (((p4 → False) ∨ p1) → (((((p1 → p5) ∧ p4) → ((p4 ∧ False) ∨ p2)) ∧ ((p1 ∨ True) ∧ True)) ∨ (False ∨ (p1 ∨ False))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- False on the left can always be used.
    apply False.elim h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809947051188597571832843932077 : (((p5 → ((((p5 ∧ p1) ∨ ((((p3 → p2) → (p4 ∨ (p3 ∧ p4))) ∧ (False ∧ p4)) ∨ (p5 → p4))) ∨ True) ∨ (p4 ∨ (p5 ∧ p4)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694788016820631685850310877759 : ((((True → (((p5 → p3) → ((p1 ∧ (True → (False → True))) ∨ p4)) → p1)) ∨ (((p3 ∨ ((False ∧ True) ∧ p4)) ∨ p3) ∨ (p5 ∨ True))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_218192820753693816289785419111 : (((p2 ∧ True) ∨ (p2 ∧ p3)) → ((((True ∨ p3) → ((((p2 ∨ p2) ∨ p2) ∨ (p5 → p1)) ∨ p1)) → p3) ∨ (((p2 ∨ p4) → True) ∨ False))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695682735457517416996184711669 : (((((False ∨ (p1 ∨ (True → True))) ∧ (False ∨ (p1 ∨ ((p1 ∧ p1) → p2)))) → ((p4 ∧ p1) ∧ ((True → (p1 → p2)) ∨ (p1 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344410001796422868872839485369 : (p2 → (p5 ∨ (((p3 → p5) ∧ ((False → (p3 ∧ (p2 → (p5 ∨ ((((p4 ∨ (p1 ∨ True)) ∨ p3) ∧ (p1 → False)) ∨ p5))))) → p5)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51858623078625250794577950927 : ((((((False ∨ False) ∨ (((p3 ∨ ((p4 → p2) ∧ p2)) ∧ p1) → p2)) ∧ p1) ∨ p3) ∨ (((False ∨ ((p4 ∧ p2) → True)) → False) → False)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ ((p4 ∧ p2) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310105432195803025576722919712 : (p2 ∨ ((p2 ∨ (p3 → ((((p4 ∨ p2) → ((p1 ∧ True) ∨ True)) ∧ True) ∨ True))) ∧ (((p4 ∨ (p5 → (p3 ∧ p2))) ∨ p5) ∨ (p2 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726244116855560165138313814035 : (((((False ∨ p2) ∨ p4) ∨ (p1 ∧ (((((False → (False ∧ (p3 ∨ (p5 ∧ p2)))) → p4) ∧ (p1 → p2)) → ((True ∧ p5) ∧ p1)) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166709692940639450620749469809 : ((p3 → (((p4 → (((p1 ∨ p2) → (p5 → p4)) ∨ p5)) ∧ (p4 → p1)) → (p5 ∧ False))) ∨ (p3 → (p5 ∨ ((False → (p2 → True)) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748029307035199394327192818790 : ((((p1 → p1) → ((((((p2 ∧ ((True ∧ p4) ∨ (((False ∧ False) → False) ∧ p3))) ∧ p5) → False) ∨ (p4 → True)) ∨ (p4 ∨ False)) ∨ p2)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801261543624010411402722602984 : (((p2 → (((p4 ∨ p1) → ((((p5 ∨ p1) → p3) ∨ p2) ∧ ((True → p3) ∨ (False → False)))) → ((p3 ∧ (p1 ∨ (False ∨ p2))) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205054749608841141054507486142 : (((p1 → (True ∧ (p4 ∨ True))) → p4) ∨ (p5 ∨ ((((p4 → (p4 ∧ ((p1 → (p2 ∨ True)) ∧ (False → p4)))) ∧ p2) ∧ p5) → (p2 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353900397775803900670635453348 : (p4 → (p2 → ((True → ((((((((p4 → False) ∧ p5) → (p2 → (p5 ∨ p3))) ∨ p5) → (p3 ∧ p2)) → p2) → False) ∧ (p1 ∧ True))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347326383815785086307959036038 : (p3 → ((False ∨ (p5 ∨ (((p3 → p3) → (p4 ∨ p4)) → p2))) → (((False ∧ (p2 ∧ (p1 ∨ p4))) ∨ p3) ∨ (((p4 ∨ False) → False) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774035495325513896499470913495 : (((False ∨ ((((((((p1 → False) → p1) ∨ p1) ∨ ((p2 ∧ (True ∧ (False ∧ True))) → p3)) ∨ p1) ∨ (p2 → p5)) ∧ p1) ∨ (p3 ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184132936873093114753055423797 : (((p2 ∧ (p2 ∧ ((p4 ∧ p1) ∧ (p3 ∨ (p3 ∨ p5))))) ∨ p2) ∨ (((p3 → ((p2 ∧ False) ∨ (True ∨ p2))) ∧ p5) → (p1 → (p4 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42290673148090267739085920918 : (((p2 ∧ (((((False ∧ p1) ∧ p5) ∧ (True ∧ ((False → False) ∨ False))) ∧ (((True ∧ (p5 ∧ (False ∨ True))) ∧ p2) → p3)) ∧ p4)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118697931082957484860851095766 : ((p5 ∨ ((p2 ∧ (p4 ∨ (p1 ∨ (((p5 ∨ p3) ∨ ((True → p3) → p2)) ∧ (True → (((p4 ∧ False) → False) ∨ False)))))) ∨ True)) ∨ (p4 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60825695240384411328910351825 : ((True ∧ (p5 ∧ (p3 ∨ (p3 → (((((((False → True) → p1) → (False ∧ (p1 → p4))) → True) ∧ p2) ∨ ((p5 ∧ p5) → p2)) ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219999060284871567745709073610 : ((p5 → (p5 ∨ (True ∨ p5))) → ((p2 ∨ (p2 ∨ (False ∨ ((p2 → p5) ∨ (((p5 ∨ False) ∨ (True ∨ (p2 ∧ p5))) ∨ (p1 ∧ p2)))))) ∨ p3)) := by
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
theorem thm_5_vars_149691365536103894023215165590 : ((p5 ∧ ((((((p1 ∨ ((p3 ∧ False) ∨ False)) ∨ True) ∨ p3) ∧ True) → p3) ∧ ((p2 → p5) ∧ (p5 ∨ p5)))) ∨ ((False ∨ (p5 ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52775552736681810388075789750 : ((((((True ∨ p3) ∨ (p5 ∧ p2)) → (p1 ∧ (p4 ∨ p1))) ∧ (True ∨ p4)) → (((p3 ∧ p5) ∨ (False ∨ (False → (p3 ∧ True)))) ∨ True)) ∨ p4) := by
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
theorem thm_5_vars_726191541825231114951577864647 : (((((p5 ∧ p2) ∨ p2) ∨ (((p3 ∨ (p1 → p3)) ∨ p4) ∨ (False → ((((p1 ∧ p5) ∧ (p4 ∨ p1)) → False) → ((True ∨ p3) → False))))) ∨ p1) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203086160681643617072392803126 : (((False → p2) → ((p5 → p5) → True)) ∧ (((p2 ∧ False) ∧ ((p5 ∧ (((p1 ∨ p3) ∨ p4) ∨ (False ∨ (True ∧ False)))) ∨ p1)) ∨ (False ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675512257645189028054252382386 : (((((((((p4 ∧ (p1 → True)) ∨ p2) → p1) → ((p1 ∨ (True → p1)) → True)) ∧ p5) ∧ (p4 ∧ True)) ∧ (p1 ∨ ((p5 ∨ p3) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601117126918451157796372190817 : ((((p1 ∧ (p2 ∨ (((p5 ∧ (((p4 → False) ∧ True) ∨ p3)) → True) → ((True ∨ p4) → (((p5 ∨ True) ∧ (p3 ∨ False)) ∧ True))))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184294817654734856308537442453 : (((((p1 ∧ p4) → p3) ∧ (p4 → ((p2 ∧ p5) → p4))) → p5) ∨ (((p3 ∨ (True ∨ p4)) ∧ True) ∨ ((p4 ∧ ((True → p4) → p4)) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_198476265232099145354389704168 : ((p5 ∧ (p5 → (p3 ∨ (p1 ∨ (p1 ∧ False))))) ∨ ((p2 ∧ ((((p1 → False) ∧ p3) → p2) ∧ ((p2 ∧ (p5 → False)) ∨ (p5 ∧ p4)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147728708769370137327792453261 : (((((p2 ∧ True) ∨ (p3 ∨ (p2 ∨ True))) ∨ (((True ∧ False) → (False → ((p4 ∨ True) → p5))) ∧ p3)) → p1) ∨ (((p1 ∧ p2) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59613862897204144425175456191 : (((p4 → p5) ∨ (p3 → (p4 ∧ ((False ∧ (False ∧ (True ∧ (p5 → p3)))) ∧ (((((p3 ∧ False) → p3) → p2) → p4) ∨ (p2 ∨ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148785073409806094966764865344 : (((False ∧ (p1 ∧ ((p5 ∨ True) ∨ False))) ∨ ((((p5 ∨ p4) → p3) ∨ ((p4 ∨ (p1 → p3)) → p5)) → p1)) ∨ (((p5 → False) ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314853694949041204782269600604 : (p3 ∨ (((True ∨ (p1 ∧ ((p2 → p5) → (p3 → (p3 → False))))) ∧ p3) → ((p5 ∨ ((True ∧ (p3 ∧ ((p1 → p4) → p1))) ∨ p2)) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164999870957301193875351633857 : ((((p3 ∧ ((p5 ∧ (p4 ∨ (p1 → p3))) → p2)) ∨ (p3 ∨ ((True → p3) → p4))) → False) ∨ ((p2 ∧ (p5 ∨ False)) → (p5 → (p2 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



