variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116188426770986554612822869796 : ((((False ∧ True) ∧ p1) ∨ ((((p5 → p4) → p3) ∨ ((p5 ∧ p4) ∨ False)) ∧ (p4 ∨ (p3 ∧ ((p2 ∨ False) ∨ (True ∨ p5)))))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149664422099997458720652458285 : ((p4 ∧ (p1 ∨ ((((p5 ∧ p3) ∨ (p4 ∨ ((p2 → p1) ∧ p3))) ∧ p4) → (((p2 ∨ p5) → True) ∧ p1)))) ∨ (True ∧ ((True ∨ p5) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345534735218625294794560501754 : (p3 → ((((True ∧ (p4 → p5)) ∨ ((p4 ∧ True) → p2)) ∧ (((p1 → ((p4 → p5) → ((p4 → p2) → (p4 ∧ False)))) ∨ True) ∧ p5)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40651586428300887231850178600 : (((((((True ∨ (False ∨ ((p4 ∨ (p1 → False)) ∨ (p2 ∨ p2)))) ∨ ((p1 ∨ (p3 ∨ p4)) ∨ p2)) → p5) ∧ (p4 ∨ p3)) → False) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626625983039413869821543849937 : ((((p4 → (p1 ∨ (((((p5 ∧ (p4 → False)) → ((True ∧ p4) → ((True ∨ p1) ∧ p1))) ∨ (p1 ∧ p2)) ∧ (False ∨ p5)) ∧ False))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_53846963502155474445406943719 : ((((p1 ∧ (p2 → (p5 ∧ p4))) → ((p4 → False) → False)) ∨ (((True ∧ (((False → p3) ∨ p1) ∨ p5)) ∧ p3) → ((p4 → False) → p3))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752395974383549209388064973555 : (((False ∧ ((((True → p3) → (((False ∧ True) ∨ p5) → ((p1 → True) ∨ ((False ∧ (p4 ∨ False)) ∨ (p1 ∨ p3))))) → (p1 → p5)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765994714518092476413662935318 : (((p4 ∧ (((p1 → p1) ∧ False) ∧ (((p5 ∨ p2) ∨ ((p3 ∨ False) ∨ p5)) ∧ ((True → (p5 ∧ True)) → (((False ∧ p1) ∨ p3) → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197225396708650508218249435196 : ((((p4 ∨ ((p2 ∨ False) → p5)) ∨ p4) → False) ∨ ((p2 ∧ ((p1 ∧ p1) → (((p5 ∨ p1) → True) ∧ (False → True)))) → ((p2 ∨ p4) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227008513907439069811281933613 : (((p1 ∨ p4) → p1) ∨ (p1 ∨ ((p3 ∧ p4) → ((((((((p2 → p1) → (p5 ∨ (p2 → False))) → True) ∧ p5) ∧ p3) ∧ p5) ∧ p2) ∨ p4)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123500711667327193058211521225 : ((((((p4 ∧ (False ∧ (p3 ∧ p3))) → (p2 → False)) → False) ∨ ((p1 → False) → p5)) ∧ (p4 → ((p4 ∨ (p3 → p2)) ∨ p1))) → (p5 ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232664932874514871786845481663 : ((p1 ∧ (p2 ∧ p1)) → ((p4 ∨ ((p5 → (((False ∨ ((True ∨ (p5 ∧ p3)) → False)) ∧ p1) ∨ ((p1 → p4) ∨ True))) ∧ p2)) ∧ (False → p5))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151917885213041737724833746503 : (((((False ∧ p1) → (p4 ∨ (p3 ∧ ((p2 ∨ True) ∧ p1)))) ∧ p4) ∧ (p2 ∨ (p2 ∧ (True ∨ (True → False))))) → (((p1 ∧ True) ∨ p5) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1790719967996677972144229570 : (((False ∧ (((p5 ∨ p5) ∨ False) ∧ (False ∧ p5))) ∧ ((((p4 ∨ (p5 ∨ (p5 → False))) ∨ p1) ∧ p2) ∨ p5)) ∨ ((p1 → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172370381538152766756747708877 : (((p4 ∧ (p3 ∨ ((False ∨ p4) ∨ p4))) ∨ ((((p1 → True) ∧ False) ∧ p5) ∧ p1)) ∨ ((False → (p1 → p3)) ∨ (p4 ∧ ((p5 ∨ True) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197501421279658415975372964989 : (((False ∨ (p1 ∨ (True ∨ True))) ∧ (False ∨ False)) ∨ ((((True → ((p4 ∨ p1) → p5)) ∧ ((p2 → p4) → (p3 ∧ p3))) ∧ p5) → (p2 ∨ p5))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161163538097224864631035016467 : (((p2 ∧ p5) ∨ (((p1 ∧ True) ∨ ((p1 ∧ p1) ∧ ((p5 ∧ p5) ∨ (p5 ∧ False)))) ∨ (p2 ∨ False))) → (((True ∧ p1) ∨ p2) → (p4 ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
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
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- Conjunctions on the left can always be decomposed.
          let h17 := h15.left
          let h18 := h15.right
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h19 =>
            -- Conjunctions on the left can always be decomposed.
            let h20 := h19.left
            let h21 := h19.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h22 =>
            -- Conjunctions on the left can always be decomposed.
            let h23 := h22.left
            let h24 := h22.right
            -- False on the left can always be used.
            apply False.elim h24
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h27 =>
          -- False on the left can always be used.
          apply False.elim h27
  case inr h28 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- Conjunctions on the left can always be decomposed.
          let h35 := h34.left
          let h36 := h34.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h37 =>
          -- Conjunctions on the left can always be decomposed.
          let h38 := h37.left
          let h39 := h37.right
          -- Conjunctions on the left can always be decomposed.
          let h40 := h38.left
          let h41 := h38.right
          -- Disjunctions on the left can always be decomposed.
          cases h39
          case inl h42 =>
            -- Conjunctions on the left can always be decomposed.
            let h43 := h42.left
            let h44 := h42.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h45 =>
            -- Conjunctions on the left can always be decomposed.
            let h46 := h45.left
            let h47 := h45.right
            -- False on the left can always be used.
            apply False.elim h47
      case inr h48 =>
        -- Disjunctions on the left can always be decomposed.
        cases h48
        case inl h49 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h50 =>
          -- False on the left can always be used.
          apply False.elim h50



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185258908993671831679960771336 : ((p1 ∧ ((p4 ∨ ((p4 ∧ p2) ∧ p3)) ∧ (p5 ∨ (p1 ∨ True)))) ∨ (True ∨ (((p2 ∧ ((p3 ∨ (p5 → False)) → p2)) → p2) ∨ (p3 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157653280999686841966112613356 : ((((((p5 → (p4 → (p2 ∨ True))) → ((False → p1) ∧ p4)) ∨ True) ∨ p1) ∨ (p4 → (p1 ∨ True))) ∨ (p4 ∨ ((True ∧ (p1 → True)) ∧ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346340741762334413868759008236 : (p3 → ((((p5 ∨ ((False ∧ False) → p2)) → (False → p1)) ∧ (p1 → ((p5 → ((p3 ∨ p4) ∧ p5)) → (p5 → (p1 → p4))))) ∨ (False → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179351060843926110489811437340 : ((p2 ∨ ((((p5 → True) ∧ (True ∨ ((p3 ∧ p5) ∧ p2))) ∨ p3) ∧ p2)) ∨ ((p3 ∨ (p5 ∧ p5)) → ((((p2 ∨ False) ∨ True) → False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701170339898423731094421435241 : (((((((p2 → False) ∧ (False → p3)) ∧ True) ∧ (False ∧ p1)) ∧ ((((p2 ∧ p2) ∨ p3) ∨ (p5 ∨ (p3 → ((False ∨ True) ∨ False)))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40118128880795239749151066264 : ((((((p3 → p3) ∧ (((True ∨ False) → (p4 → p3)) ∨ (False ∨ ((p4 ∧ (p2 ∨ p4)) ∨ (p2 → p3))))) → (p4 → p1)) ∧ p2) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617530517618609096118732643780 : ((((((True ∨ p1) ∧ (p5 ∧ (p5 → p1))) ∧ ((True ∧ (((True → False) ∧ (p2 → (p5 ∧ False))) → (p4 ∨ (p1 ∨ p3)))) ∧ p4)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_260721410643555240716813039811 : ((p3 → p4) → ((True → (((p3 ∧ p2) ∨ True) ∧ (((p3 → ((p1 ∨ False) → p4)) ∨ (False ∧ ((p1 ∧ p4) → p4))) ∧ False))) → (True ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9686914504442478040250608389 : ((((False ∨ p3) ∨ (((False ∨ ((p5 → p5) ∧ (p1 ∨ ((True ∧ p5) → (p1 → p4))))) ∧ p2) ∨ ((True → (p2 ∧ False)) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164865382106321597995996902784 : (((p3 ∨ ((p4 → p4) → ((((p2 ∧ p3) → True) ∧ (p5 ∨ False)) → (p5 → p1)))) ∨ p4) ∨ ((p5 ∨ p3) → ((p5 → p5) ∨ (p3 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256787059174931601198312641387 : ((p1 ∨ p2) → ((p3 → ((False → (p1 ∨ p5)) ∧ p3)) → ((((p2 ∨ (p3 ∨ p5)) → p3) → p5) → (p4 → ((p5 → p1) ∨ (p4 ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773489291147238881047868884639 : (((False ∨ (((p4 → (p5 → (((p3 ∧ (p3 ∨ p1)) ∨ False) ∨ ((p1 ∨ p1) ∨ ((False → True) ∧ (p3 ∧ p3)))))) ∧ (p1 → p5)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300062966101757261088148219249 : (False ∨ ((((((p2 ∨ (p1 → p1)) ∨ ((p3 → p2) → ((p4 → True) → p2))) ∨ (((False ∧ p5) → p2) → p3)) → p4) ∨ True) ∨ (p4 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136487850688234670448109041063 : ((((p3 → p5) ∨ p2) ∧ (p5 → ((((p2 ∧ p1) ∧ (p2 → (((True ∨ p5) ∧ p4) → (p5 ∧ p4)))) ∧ True) ∧ p4))) ∨ (p2 ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620197072549618934893455808015 : (((((p3 ∧ p3) ∨ ((p1 ∨ (((p4 ∨ ((p5 → ((p3 ∨ p1) ∨ (p3 → (p5 ∧ p4)))) → True)) ∨ p4) ∧ (p3 ∨ p2))) ∧ True)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_605324283789745979082954175041 : ((((p3 → (((((((False ∨ p1) → p5) ∨ p1) ∨ p2) → (p5 ∧ (p2 ∧ ((p5 ∨ p1) → p1)))) ∨ (p1 ∨ (p5 ∨ p2))) ∨ p3)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313975418793220887694169604570 : (p3 ∨ (((((p2 ∧ False) ∨ (p1 → (p1 ∨ ((p2 ∧ p2) ∧ p2)))) ∨ True) → ((p1 ∧ (p3 ∨ (False ∨ p5))) → (False ∨ p1))) ∨ (p3 ∧ p3))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
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
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643152970035973914651476210449 : ((((p3 ∧ ((((p4 ∧ ((p3 ∨ ((p1 ∧ (p4 ∧ p1)) ∨ ((p4 ∧ p4) → p3))) ∧ p1)) ∨ p2) ∨ ((p2 → False) → p1)) → p1)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48954887260515797496037819825 : ((((p5 ∨ (((p4 → p5) ∧ ((p2 ∨ p5) ∨ ((p1 ∨ p3) ∧ (p2 ∨ ((p5 ∨ p3) ∨ p1))))) → p4)) ∧ p2) ∨ ((False ∧ p4) → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42024669168385823289968368590 : ((((p1 ∧ False) ∨ (((p2 ∨ (((p4 → p5) ∧ p1) ∨ p1)) ∧ p3) ∧ ((p5 → ((((p1 ∧ p4) ∨ p1) ∧ False) ∧ p3)) → p1))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780165972262777198878604244203 : (((p2 ∨ ((((p3 ∧ p1) ∨ p5) → (((False → (((p5 ∨ p1) ∧ p2) → (p4 ∧ False))) ∨ p3) → (p3 ∧ p3))) ∧ ((True → p4) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231681873637731872682717020698 : (((p1 ∧ p2) → p2) → (((((p2 ∧ p2) → p5) → p3) → (p4 → p1)) → (p3 → (p5 → ((p5 ∧ p3) ∧ (p5 ∨ ((False ∧ False) → p3))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245247789307534772634670681866 : ((p2 ∧ p1) ∨ ((p4 ∧ (((False → p4) ∨ False) ∧ False)) ∨ (((((True → False) → (True → (True ∨ p2))) ∧ False) ∨ p4) → ((p1 ∨ p4) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673249461393793921576465060752 : ((((((p1 ∧ (p1 ∨ p5)) ∨ (p4 ∨ (p1 ∨ p3))) ∧ ((p3 → (((p2 ∨ p5) ∧ p5) ∧ p4)) ∨ (p3 → p5))) → (p3 ∧ (True ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7997410247329852630330023597 : ((((((p4 ∨ ((p3 → True) → (p4 → ((p2 ∨ (p3 ∧ ((p5 → True) → p5))) → p3)))) ∨ (False → (p1 ∧ False))) → p4) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179456043808715398433143164730 : ((p5 ∨ ((True ∨ p2) ∧ (((((p2 ∧ p5) → p5) ∧ p5) → p2) ∧ p2))) ∨ (False ∨ ((((p1 ∧ (False ∧ (False → False))) ∨ p4) ∨ p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52960013578538802357019808221 : ((((p1 → ((p2 ∧ True) ∧ (p3 ∨ ((p3 ∨ False) ∧ p1)))) ∨ p4) ∧ (False ∨ (False → ((p1 ∧ p1) ∨ ((False ∧ (p2 → p4)) ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645898038139157537309999521000 : ((((True → ((p4 → ((p4 → p2) → ((((p5 → True) → ((p1 ∧ False) → (True ∨ (p1 ∨ p4)))) ∧ False) ∧ (p4 ∨ False)))) ∨ p2)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_918913499388288121263381518165 : ((((((p3 → p3) → (p5 → ((((p2 → True) ∧ False) → True) ∨ False))) → False) ∧ ((p2 → ((p3 → False) ∨ False)) ∨ ((False ∨ True) ∧ p4))) → p2) ∧ True) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((p3 → p3) → (p5 → ((((p2 → True) ∧ False) → True) ∨ False))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h5
    -- False on the left can always be used.
    apply False.elim h9
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
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : ((p3 → p3) → (p5 → ((((p2 → True) ∧ False) → True) ∨ False))) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- Implications on the right can always be decomposed.
        intro h17
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h18
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h19 := h2 h15
      -- False on the left can always be used.
      apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264661759862159678957455830452 : (True ∧ ((p3 → (p3 → p2)) → (((p4 → p2) → (((True ∨ p3) → p5) ∨ True)) ∨ ((((((True ∨ p3) ∧ p2) ∧ p4) ∧ p1) ∧ p3) → p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_115834475320894135550007756959 : (((False ∧ ((p1 ∨ p5) ∨ p5)) ∧ ((((p5 ∧ ((((p4 ∨ (p2 ∧ p2)) ∨ (p4 ∧ p2)) ∨ p4) → p2)) ∧ p1) ∨ p2) → p2)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717511979204222059163390512589 : ((((p2 → ((p3 → p3) → p4)) ∧ (((p5 ∧ p1) → p3) ∧ (p3 ∧ (p3 → ((p1 → (p4 ∧ ((p4 ∧ False) ∨ (p1 ∨ p2)))) → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138431408312019213364045861667 : ((p5 → ((((p2 ∨ (((False ∨ p3) ∨ (p1 ∨ p3)) ∨ False)) ∨ (p5 ∨ p3)) ∨ p4) ∨ (p1 ∨ ((p3 → p5) ∨ p5)))) ∨ ((True → p3) ∨ p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187368622617843581331069829482 : ((p3 ∧ (((False ∨ p1) → True) ∧ (p3 → (p2 → (p3 → p1))))) → ((p1 → ((False → p4) ∧ True)) ∧ ((p4 ∧ p3) → (False ∨ (p4 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230435587498676314760527756554 : (((p4 ∨ p4) ∧ p5) → ((p1 ∨ ((p3 ∨ (((p2 ∨ True) ∧ p5) ∧ ((False ∧ (True ∨ (p1 ∨ (True → p4)))) ∨ p4))) ∧ (p2 ∨ p4))) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69017077847497728391162254587 : ((p5 → ((p4 ∨ (((p1 ∧ p4) → (p4 ∨ p3)) ∧ ((((p3 ∧ p4) ∧ ((p5 → ((True ∧ p2) ∨ p3)) → p1)) ∨ False) ∨ True))) ∧ p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697260084527709665217018517992 : (((((p2 ∧ p5) ∧ (((p4 ∧ ((True → False) ∨ p2)) ∨ True) ∧ True)) ∧ (((p4 ∨ (p1 ∧ ((p5 → p2) ∨ p2))) ∨ (p4 → p1)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191088713962454009858663121293 : ((((p5 ∧ p4) ∨ p1) ∧ (p3 → ((p1 ∨ p3) → p5))) ∨ (((True ∨ p4) → (((((p3 → p3) ∨ p4) ∧ (p1 → p3)) ∨ p5) ∨ p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187605944713345985354989242925 : ((p4 ∨ ((p5 ∨ (p1 ∧ ((p1 ∧ p4) ∨ False))) → (p3 → p1))) → ((p2 → p5) ∨ (p4 → ((p4 → False) → (p3 → ((p2 ∧ True) ∧ p2)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- False on the left can always be used.
    apply False.elim h7
    -- True on the right can always be proven directly.
    apply True.intro
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h14 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h15 := h12 h14
    -- False on the left can always be used.
    apply False.elim h15
    -- True on the right can always be proven directly.
    apply True.intro
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h16 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h17 := h12 h16
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227870450819138378355355870115 : ((p2 ∧ (p3 ∨ p3)) ∨ (p1 ∨ ((((False ∧ p4) ∧ (p1 → True)) ∨ ((p2 ∧ p4) → (((p4 ∧ (False ∨ False)) ∧ p1) → (p2 ∨ p2)))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_909907289445941748361962303623 : ((((True → (((((False → True) ∧ p4) ∨ ((p4 → (p4 → p5)) ∨ (p2 ∧ p5))) ∧ p2) ∧ False)) ∧ ((p2 ∨ (p5 → (p2 ∧ p5))) ∨ True)) → p3) ∧ True) := by
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
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- We need to get the right conjuct of h7 based on <expert-advice>.
      let h8 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- False on the left can always be used.
    apply False.elim h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118845513971798428693635622607 : ((True → ((p4 → (((((p2 ∧ p5) ∨ (p1 ∨ p3)) ∧ False) ∧ ((p2 ∨ True) ∧ p4)) ∨ p1)) ∧ (((False ∨ p4) ∨ p5) → True))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224616654249120666835790771570 : ((p3 → (True ∧ True)) ∧ (((((True ∨ ((p4 → p2) ∨ ((p4 ∧ True) ∨ True))) ∧ False) → (True → p3)) → ((p1 ∨ p1) ∧ True)) ∨ (p4 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615890159640378253676983081102 : (((((False ∧ ((p2 ∧ p4) ∧ ((p4 ∧ p1) ∨ (((False ∧ p1) ∧ True) → p2)))) ∨ (p1 ∨ (p4 ∨ ((p4 ∧ p1) → (True ∧ p3))))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112878172975343527094489314226 : ((((p3 → (p4 → p3)) → ((((p1 ∨ (p2 ∧ (p5 → p3))) → p5) → p5) ∧ ((p1 ∨ (True ∨ (p3 ∨ p3))) → p2))) → p2) ∨ (p1 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → (p4 → p3)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (p1 ∨ (True ∨ (p3 ∨ p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195415646603287933959425672348 : (((p4 ∨ (p2 → p2)) ∧ ((False → False) → True)) ∧ (((p1 → (p5 → (((p3 ∧ False) ∨ p1) ∨ p2))) → ((p5 ∨ p2) ∧ (True ∧ False))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55684974427753624396731173571 : (((((p2 ∨ p4) ∨ p2) ∨ True) ∧ ((p5 ∨ (((True ∧ (p4 → p5)) → (p3 ∧ ((p4 ∧ p4) ∧ p1))) → ((p3 ∧ p3) → True))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214497397921170529787450643589 : (((p2 ∧ p4) ∧ (False ∧ p4)) ∨ (True → ((False ∨ p1) ∨ ((True → ((True ∧ p4) → p4)) ∨ (False ∨ ((p2 → (p1 ∨ p1)) → (p5 ∨ p4))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62010010411118239025235179276 : ((p2 ∧ ((True → ((p2 ∨ p5) ∨ p3)) → ((p3 → p5) ∧ ((p5 → (True ∧ False)) ∨ (((False ∧ (p5 → p1)) ∧ True) → (p5 → p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775630293291306055075866103858 : (((False ∨ (False ∨ (p1 → ((((((p1 → p3) ∧ (p4 → p3)) ∧ ((False → (p4 ∨ False)) → (p1 ∨ p2))) → False) ∧ (p1 ∨ p1)) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164556638626994290632826195353 : (((((True ∧ ((p5 ∧ p3) ∧ p4)) → p2) → ((((p4 ∨ p5) ∨ True) → p5) → p1)) ∧ True) ∨ ((True ∧ (p4 ∨ p3)) ∨ ((p5 → True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112522406650832233245669603159 : (((((((p3 → p5) → p1) → (True → (((((p4 ∧ p5) ∨ False) → (p4 ∨ True)) ∨ p1) ∧ (p1 ∨ False)))) → p3) → p3) → p1) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227052717061200672416354153112 : (((p2 ∨ p5) → False) ∨ (p3 ∨ ((p2 ∨ p4) → ((p4 ∧ p1) → (False ∨ (p2 → ((p1 → (p2 → p4)) ∧ ((p4 → p4) → (p2 → True))))))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- One of the premise coincides with the conclusion.
    exact h11
    -- Implications on the right can always be decomposed.
    intro h15
    -- Implications on the right can always be decomposed.
    intro h16
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214693590874140296437293910212 : (((True ∧ p2) ∨ (True → p3)) ∨ ((((p4 ∧ ((p1 ∧ p3) ∨ ((False ∧ True) → p5))) ∨ ((p2 ∨ p2) → p3)) → p4) ∨ ((False → p4) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178725035071389740456743270512 : (((((p1 ∧ p2) ∨ p2) → False) → (p5 ∧ (p2 ∧ (False ∨ (False ∨ p5))))) ∨ ((((p4 ∨ p2) → p4) → (p4 ∧ ((p4 ∧ p4) ∧ False))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729591762920384077763799269471 : (((((p4 ∨ p4) ∨ True) → (((p4 → (((p2 ∨ (False ∧ False)) → ((True → True) → p1)) ∨ p2)) → ((True ∨ p4) → p5)) → (p3 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309816234707574018591040941588 : (p2 ∨ ((p1 ∨ ((p4 → ((False ∧ p4) ∧ p4)) ∨ ((p3 → (((True ∨ p5) ∨ (True ∧ p4)) ∨ False)) → p1))) ∨ (((p2 ∧ p3) ∧ False) → p2))) := by
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
theorem thm_5_vars_722949981631640278207484223375 : (((((p5 ∧ p2) ∨ False) ∧ ((((p5 ∧ ((((p5 ∨ p3) ∨ (False ∧ (p1 ∨ ((True ∨ p5) ∨ p4)))) ∧ p5) → p4)) ∧ p5) ∨ p3) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60221222320667923904057338885 : (((True → p1) → (p4 → (((True ∧ p4) → p2) → (((((True ∧ p1) → False) → (((p4 ∨ p3) ∨ (p5 → p4)) → p3)) ∧ True) ∧ p1)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h8 : (True ∧ p1) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h9 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h10 := h1 h9
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h11 := h4 h8
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h14 : (True ∧ p1) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h16 := h1 h15
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h17 := h4 h14
    -- False on the left can always be used.
    apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h18 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h19 := h1 h18
  -- One of the premise coincides with the conclusion.
  exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678192585428930512504089803263 : (((((((p3 ∨ p4) ∧ ((p1 ∨ False) → p3)) → (True ∧ p5)) ∧ ((p3 ∨ p1) → (p1 → (p4 → p3)))) ∨ (False → ((p3 → p2) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203843393770438413060562001328 : ((False → ((p1 ∧ p1) ∨ (p1 → False))) ∧ (p2 ∨ (((True ∧ p3) ∧ ((p3 → True) ∧ (p1 ∧ (p4 → (False → True))))) → ((p3 → False) → False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h12 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h13 := h3 h12
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177711972507856778952715787070 : ((((p4 → (((p2 → p1) → True) → False)) ∧ ((p4 → p4) ∧ p2)) ∧ p5) ∨ ((((p5 ∧ p2) ∧ (p1 ∨ (p5 ∨ p3))) ∨ (p2 → p2)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131286854593593008350766007340 : (((p5 ∧ (p2 ∧ ((False ∨ p5) ∧ p4))) ∨ (((((p2 ∧ ((False ∨ p4) ∨ p5)) → True) ∧ p3) ∧ p4) → (False → False))) ∧ ((p1 ∧ p1) → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42495172479675017542214718608 : (((False ∨ ((((p5 ∧ (p4 → p4)) → p5) ∨ (p1 → (((p2 → (((p1 → True) ∨ False) ∨ p1)) ∨ p2) ∧ (False → p2)))) → p5)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624383256827937918835368476275 : ((((p3 ∨ ((p4 ∧ p3) → (p1 ∨ (p1 → (p5 ∨ ((p4 → (False ∧ ((True ∧ p3) ∨ False))) ∨ (False ∨ (p5 ∨ (p2 ∨ p1))))))))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49289355491031988452168659674 : (((p5 ∧ ((p3 ∨ False) ∧ (((True ∨ (False ∧ ((((False ∧ p5) ∧ p4) ∨ p5) ∨ p1))) ∧ False) → (p3 ∨ p1)))) ∨ (False ∨ (p5 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246751937199710465334061281724 : ((p5 ∧ p5) ∨ ((p3 ∨ (((((p3 ∨ ((p5 ∧ p5) ∧ (((p5 ∧ p2) → p5) → (p4 ∨ p5)))) ∨ True) → False) → p2) → p3)) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16303565073746034509903763817 : ((((((p3 ∨ (p1 ∧ (p3 ∧ p2))) ∧ (True → p1)) → (p4 ∨ p5)) ∨ ((p1 ∨ p4) → (False → (p4 ∨ True)))) ∧ ((True ∨ False) ∨ False)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184755311401819209207914885911 : ((((False → p5) → (p4 → False)) ∧ ((p5 ∨ p2) ∨ (p1 ∧ p3))) ∨ (((p3 ∨ ((p3 → (True → p5)) ∧ p4)) → ((p4 → p3) → p3)) ∧ True)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323067033242870403357268033618 : (p5 ∨ (((p2 ∨ ((((True → True) → (True → p3)) → (p4 ∨ (True ∨ ((p4 ∨ p2) ∧ p2)))) ∧ ((False ∨ p1) ∧ p4))) ∨ True) ∧ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45162343845572120118676666515 : (((True ∧ ((False ∧ (((True ∨ True) ∨ p5) ∧ ((True → ((p2 ∨ (p2 → (p1 → p2))) ∧ p2)) → p2))) → ((p4 ∨ p2) → p3))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251011472242953029980259644606 : ((p1 → p5) ∨ (((((True → (p3 ∧ p1)) → (False → ((True ∧ p4) ∨ p5))) ∨ p3) → p4) ∨ (p4 → (True ∧ (((True ∨ p1) → p2) → p2))))) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678116886534048612497466449 : ((((((((p5 ∨ p3) ∧ p2) ∨ True) ∨ ((p5 → p2) ∧ p1)) ∧ p2) ∧ (True ∧ True)) → ((False ∧ (p5 → (p4 ∨ p2))) ∨ p2)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h3.left
        let h12 := h3.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h3.left
        let h15 := h3.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h3.left
      let h18 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h3.left
    let h23 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166853108602316580614614403670 : ((((((p5 ∧ p2) → p5) → ((True ∧ p3) ∨ (((True ∧ p1) ∨ p2) ∧ p1))) → p1) ∧ p4) → (p4 ∧ ((((p2 ∨ True) ∨ p1) → False) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : ((p2 ∨ True) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_394418148763901365446193622282 : (((((p4 ∨ p4) → ((p3 → ((p5 → ((p2 ∧ (p4 ∨ (p5 ∨ p2))) ∨ False)) ∨ ((p2 → p3) ∧ (p4 ∨ p4)))) ∨ (True → p4))) ∨ p2) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148897291849989369358620257057 : (((p4 ∧ ((p4 → p5) → p5)) ∨ (p2 ∨ ((False ∨ (p1 ∧ p2)) ∨ (((p5 → (True → True)) → True) ∨ p2)))) ∨ (p2 ∨ (p4 → (False ∧ True)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630085478910955213440948312729 : (((((((p3 → p2) ∧ False) → ((((True → ((p3 ∧ ((p4 ∧ (p3 ∨ p4)) ∧ p1)) ∨ p1)) → (p2 ∧ p4)) ∨ p3) ∧ p1)) ∨ p4) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255537455122836184266622501774 : ((p5 ∧ p2) → (p5 → (((p4 ∧ ((False ∧ p1) ∧ ((False ∨ p1) ∨ (p1 ∧ (p3 ∧ p4))))) ∨ (p2 ∨ p3)) ∧ ((p1 → True) → (p3 → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804676342488664841892252200736 : (((p3 → (((True ∨ True) ∧ p5) ∧ (((p2 → ((((p1 → p4) → p5) ∨ ((False ∧ (p1 → True)) ∨ False)) → (p4 → p1))) → p4) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51088399679472366172117688210 : ((((((p3 ∧ (p3 → p3)) → (((p2 ∧ (p5 → (p5 ∨ p3))) ∨ p4) ∨ False)) ∨ p4) ∧ True) ∨ ((False → False) → ((p3 → False) → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137980526683098909599013307062 : ((p5 ∨ ((p4 → (p2 ∧ False)) ∧ (p2 ∨ (((p3 ∨ False) → (p4 ∨ (p1 ∨ True))) ∨ (p2 → (True → (True → p2))))))) ∨ ((p2 ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693504767166355255644514514267 : (((((((p4 ∨ ((p3 ∨ p5) → (p5 ∨ False))) ∧ False) ∧ (p5 ∨ p3)) ∧ p1) ∨ (False → ((p5 ∧ p5) ∧ (p5 ∧ (p5 ∨ (p4 ∨ p3)))))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165515896979226897296112662281 : (((((p2 ∧ ((p5 ∧ p2) → p1)) → True) ∨ (p4 ∧ True)) → (p1 ∨ (p2 ∧ (p4 ∨ p3)))) ∨ (p1 ∨ (((p2 ∨ (p4 ∨ True)) → True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



