variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704556327326690917807096037593 : (((((True ∨ False) ∨ ((((p3 ∧ True) ∧ p2) ∨ p5) → p1)) → (p1 → (p3 → (((p2 → ((p3 → True) ∨ True)) → p2) ∨ (False → True))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_380303979790301077344319015943 : ((((((p3 ∨ (p3 ∨ ((p4 ∧ p1) ∨ ((True → (p3 ∧ ((p3 → p2) → p5))) ∨ (False → False))))) ∧ (p3 → (p4 → p3))) ∧ True) ∨ p1) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41827491115002033137713614740 : (((((p4 ∨ p3) → p4) ∧ (((((p1 → (p4 ∨ p2)) ∨ (p1 ∨ p3)) ∧ p1) ∨ (p3 ∨ True)) → (((p3 ∧ p5) ∨ p5) ∧ p3))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49882807877161894000105714226 : ((((((((True → p3) ∨ (p4 ∨ ((p1 ∨ (p3 ∧ p1)) ∧ p4))) ∧ p2) ∨ p1) ∨ (p5 ∨ False)) ∨ p1) ∧ (p4 ∧ (p5 → (p4 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347826408732478698991343375745 : (p3 → (((p1 ∧ p5) ∨ p5) → (((((p1 ∧ ((False → p1) ∨ p3)) ∨ p1) ∧ False) ∧ False) ∨ (True ∨ ((p4 → True) ∧ ((p2 ∧ p4) → p2)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316984890975258656458666418400 : (p3 ∨ (p3 → (((p3 → (p2 ∨ (((True ∧ (((p4 ∧ p5) ∧ p1) ∧ False)) ∨ ((True → p5) ∨ (p3 → p1))) → p4))) → p5) ∨ (p3 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_65752570903379110432520022506 : ((p4 ∨ ((((p5 ∨ (p5 ∧ ((p5 ∧ ((False ∧ False) ∧ p3)) ∨ (p3 → p2)))) → False) ∨ (p2 ∧ p5)) ∧ (p2 → (False → (p1 → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166438657596747257124087629928 : ((p2 ∨ ((((p1 → (((True ∨ (True → p3)) ∧ p3) ∨ (False ∨ p1))) → p4) ∨ p2) ∧ False)) ∨ ((False → False) ∨ ((p2 → (p1 → True)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117100537913897521849336320583 : (((p2 → True) → (False ∨ (((p4 → False) ∧ (p1 → ((p4 ∨ (True → p4)) ∧ (p1 ∧ p3)))) ∨ (False → ((p5 → True) ∨ True))))) ∨ (p4 ∨ p5)) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55170254419103430397286420323 : ((((((p4 ∧ True) ∨ p5) ∧ p3) → p1) ∨ (((p4 → p5) ∨ (p4 ∨ ((True ∧ ((p2 → p3) ∧ (False ∨ (False ∧ p4)))) ∧ False))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184177374937342754504686603360 : (((p2 → (False ∧ ((((p2 → False) ∨ True) → p4) → p5))) ∨ p4) ∨ (((p5 → p3) ∨ ((p5 ∨ p1) ∧ p4)) ∨ ((True ∧ True) ∨ (p2 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_147222434048231905696568431966 : (((p4 → (p3 ∧ ((((((p2 ∧ p3) → (p5 ∨ p2)) → p1) → p4) → (p4 ∧ p1)) ∨ (False ∧ False)))) ∧ p5) ∨ ((p4 → (p2 ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147488883056787555432295472948 : (((p5 ∧ (((p2 ∧ (False ∨ True)) ∧ ((p2 → (p4 ∧ p3)) ∨ ((p4 ∨ False) ∨ (p3 ∧ p4)))) ∨ False)) ∨ p4) ∨ (((True ∨ p3) ∨ p4) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160959614454670236110189284498 : ((((p5 ∨ p1) → True) ∧ (p4 ∧ ((p5 ∨ p2) ∨ ((((p1 → p1) ∨ p1) → (False ∧ p3)) ∨ p3)))) → ((((p1 ∧ p1) ∧ p3) ∨ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231132500670457001476989622104 : (((p1 ∨ p2) ∨ p4) → ((True → (False ∨ True)) → ((p4 ∧ (p4 → p2)) ∨ (True ∨ (((p5 ∧ (p1 → (False ∨ False))) ∨ (False → p5)) ∨ p1))))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178990174234832699312497791034 : (((p4 → p1) ∨ (p1 ∧ ((False ∧ (((True ∨ True) → p2) ∨ False)) ∨ p1))) ∨ (((p2 ∨ p1) → (p1 → (((p5 ∨ p1) ∧ p2) → p2))) ∨ p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319046102701908404171628883072 : (p4 ∨ ((((p4 ∨ ((p2 ∨ (False ∧ p1)) ∨ True)) ∨ True) ∨ ((p5 ∧ True) → ((p4 → (p5 → p3)) ∨ p1))) ∨ ((True ∧ (p5 ∨ p1)) ∧ True))) := by
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
theorem thm_5_vars_147092806495188862983808983822 : (((((p1 ∨ p5) ∨ p2) ∧ (True → (p4 ∧ (True ∨ (((p3 ∨ p1) ∨ (p4 → (True ∧ p3))) → p2))))) ∧ False) ∨ ((p2 ∨ (p1 ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665094925538197865339937171430 : ((((p5 → ((p4 ∧ ((((p2 ∨ True) ∧ False) ∧ (p4 → p4)) → True)) ∨ (p2 → (((False ∧ p3) ∧ (False → p5)) → False)))) → (p2 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67443936271954850216959780266 : ((p1 → ((p3 ∧ ((p5 → p1) ∧ (((p4 ∨ (p4 ∨ (p3 → False))) → (((p3 → p2) ∨ p5) → p3)) ∧ True))) ∨ ((p2 ∧ p4) ∨ p1))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3996909903464854594250922281 : (p1 ∨ ((p3 ∧ p4) ∨ (p2 → (((False ∧ p2) ∨ (((p1 ∨ p5) ∨ p1) ∨ (True ∧ p5))) ∨ (((p5 ∨ (p3 ∧ True)) → p2) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694172764201051484264386013487 : ((((((p1 → ((p4 ∧ p3) ∧ p2)) ∧ p3) → (p3 → ((p4 ∧ p3) ∧ p1))) ∨ ((p5 ∧ ((True ∧ p2) → (True → False))) ∨ (True ∨ p1))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_8978760877432543556322128 : ((((p5 ∨ p4) ∨ ((((p3 ∧ p3) ∨ p1) ∧ p2) ∧ ((p4 → True) ∨ p2))) ∨ ((((False ∧ p4) → p1) ∨ p4) ∨ p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167051686483518829659641272636 : (((((((p5 ∨ (p4 ∧ p5)) ∨ (p2 → p4)) ∧ (p2 ∨ p2)) ∧ (p1 ∧ p2)) ∨ True) ∨ p4) → ((p2 ∧ (p5 → (p4 ∨ False))) ∨ (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
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
          cases h7
          case inl h10 =>
            -- Conjunctions on the left can always be decomposed.
            let h11 := h5.left
            let h12 := h5.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h13
            -- One of the premise coincides with the conclusion.
            exact h13
          case inr h14 =>
            -- Conjunctions on the left can always be decomposed.
            let h15 := h5.left
            let h16 := h5.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h17
            -- One of the premise coincides with the conclusion.
            exact h17
        case inr h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h21 =>
            -- Conjunctions on the left can always be decomposed.
            let h22 := h5.left
            let h23 := h5.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h24
            -- One of the premise coincides with the conclusion.
            exact h24
          case inr h25 =>
            -- Conjunctions on the left can always be decomposed.
            let h26 := h5.left
            let h27 := h5.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h28
            -- One of the premise coincides with the conclusion.
            exact h28
      case inr h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h30 =>
          -- Conjunctions on the left can always be decomposed.
          let h31 := h5.left
          let h32 := h5.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h33
          -- One of the premise coincides with the conclusion.
          exact h33
        case inr h34 =>
          -- Conjunctions on the left can always be decomposed.
          let h35 := h5.left
          let h36 := h5.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h37
          -- One of the premise coincides with the conclusion.
          exact h37
    case inr h38 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h39
      -- One of the premise coincides with the conclusion.
      exact h39
  case inr h40 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h41
    -- One of the premise coincides with the conclusion.
    exact h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300607776162435070303645124790 : (False ∨ (((p5 ∨ p5) ∧ (p2 ∧ (p3 → ((p1 ∧ ((p2 → p4) → (((True ∨ p3) ∧ False) ∧ p1))) ∧ p5)))) → (((False ∧ True) ∧ False) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228032344763486436509088134100 : ((p3 ∧ (p4 → p2)) ∨ ((((p5 ∨ ((False ∨ ((p4 → (True ∨ p5)) ∧ p3)) ∧ (p4 → p5))) ∧ (p5 ∨ p2)) ∨ True) ∨ ((p3 ∨ False) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224292969488815779728429404148 : ((False → (p4 ∧ p2)) ∧ (((((p2 → (p3 ∧ p5)) → (((True ∧ (p3 ∨ p1)) ∨ True) → False)) ∧ (True ∨ p3)) ∧ False) ∨ (p4 → (p4 ∨ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324182751228754456344760201090 : (p5 ∨ ((p4 ∨ ((((p2 ∧ p4) ∨ p3) ∧ p3) → (False ∧ p2))) ∨ ((((p2 ∨ p2) ∧ False) ∧ (p1 ∧ p3)) → (p2 ∨ ((p4 ∨ p5) ∨ True))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767229283938341915349856594628 : (((p5 ∧ (((p5 → (p2 ∧ (p2 ∨ ((((False → p3) ∨ (p3 ∨ False)) → p2) ∧ (((False ∨ p5) → p4) → (p3 → p4)))))) ∨ p4) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262449563066788130910889617444 : (True ∧ ((False ∨ ((((p5 ∧ p3) ∨ (p2 ∧ True)) ∧ (p1 ∧ (((p2 → p3) ∨ (((p4 → (p2 ∧ p5)) ∨ p4) ∧ p5)) ∨ p3))) ∨ p4)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244456594837066562293952160247 : ((False ∧ p2) ∨ (((p1 ∨ ((False → True) → (p1 → p4))) ∨ p5) ∨ ((True → (((p1 ∧ ((False ∧ p2) ∨ p1)) → True) ∨ p5)) ∧ (False → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160489573428471606987145561397 : ((((((p3 ∨ p5) ∧ True) ∧ ((p4 → False) ∨ (False ∧ p4))) ∨ p1) ∧ (((p1 ∧ p1) ∧ p1) ∨ p4)) → ((p2 ∨ p3) ∨ ((p2 → p1) ∨ p5))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Conjunctions on the left can always be decomposed.
          let h14 := h12.left
          let h15 := h12.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h16 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- False on the left can always be used.
        apply False.elim h18
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- Conjunctions on the left can always be decomposed.
          let h25 := h23.left
          let h26 := h23.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h20
      case inr h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h28.left
        let h30 := h28.right
        -- False on the left can always be used.
        apply False.elim h29
  case inr h31 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h32 =>
      -- Conjunctions on the left can always be decomposed.
      let h33 := h32.left
      let h34 := h32.right
      -- Conjunctions on the left can always be decomposed.
      let h35 := h33.left
      let h36 := h33.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h37
      -- One of the premise coincides with the conclusion.
      exact h34
    case inr h38 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h39
      -- One of the premise coincides with the conclusion.
      exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218173178026048724491988709885 : (((False ∧ False) ∨ (True → p3)) → ((p5 ∨ (((False → p4) ∧ (p1 ∧ p2)) ∧ (p5 ∧ False))) ∨ (p2 → (p4 → ((p4 ∨ (p1 ∨ False)) ∨ p3))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655362137868358786658221381547 : ((((((p4 ∨ (False ∧ ((True ∨ True) ∧ ((False ∨ p1) ∧ ((p4 → (False ∧ (False ∧ p2))) ∨ p5))))) ∨ True) ∨ (True ∧ p4)) ∨ (p5 ∧ False)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750085425534243713963899827361 : (((True ∧ ((p2 ∧ ((((((p4 ∧ False) ∨ ((p4 ∧ p2) ∨ p4)) → p2) → (p4 → p3)) ∧ p5) ∨ (((p1 → p5) ∧ p2) ∨ p2))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177675014237162005644514660373 : ((((((p5 ∨ (p1 → (p3 ∧ p5))) → False) → (p1 ∨ p4)) → p5) ∧ p3) ∨ ((True ∧ (False ∧ p1)) → (False ∧ (((p3 → p1) → p4) ∨ True)))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57601144352189356077197936611 : ((((p2 → p1) ∧ p3) → ((((p2 ∨ p5) ∧ p3) ∧ p4) ∨ (((((p3 → p5) ∨ True) ∧ False) ∨ (((p2 → False) ∧ False) → False)) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783795751688981113072745773781 : (((p3 ∨ (((p5 → False) ∧ (True ∧ p5)) ∨ (((((p3 ∨ (p2 ∨ (((False ∧ p1) → p2) ∧ False))) ∨ True) ∧ (p2 ∨ p3)) ∧ p4) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112687046187382840294105013337 : (((((p4 → (((p2 ∨ ((p1 ∨ False) ∨ p2)) → p4) ∨ True)) ∨ ((p4 ∧ p5) → True)) ∧ ((True ∧ True) ∨ (p4 ∧ p2))) → p4) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666417836934058328582348266759 : ((((((((((p3 → p2) ∨ (True ∧ p3)) → (p4 ∨ False)) → (p4 ∨ True)) ∧ p2) ∨ p5) → ((p5 → p2) ∧ p4)) ∧ ((False ∧ False) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231363682978251362689440399746 : (((False → p1) ∨ p5) → (((p4 → ((p1 ∧ ((p2 → p1) ∨ (False ∧ ((p3 ∨ False) ∨ p4)))) ∨ p3)) ∨ p5) → ((p5 → (p1 → p2)) ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149436230580546861577601558646 : ((True ∧ (p2 → (p3 → ((p3 ∨ p2) ∧ (((p1 → p2) → p3) → (((p2 → p4) → False) ∨ (False ∧ p5))))))) ∨ (True ∧ (True ∨ (p5 → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150203960084477660726928326684 : ((p2 → ((((p5 ∨ (((p1 ∨ p4) ∨ True) ∧ p4)) ∧ p3) ∧ (p1 → (p4 ∧ p4))) ∨ (False ∨ (p5 ∧ p1)))) ∨ (True ∨ ((p4 ∧ False) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40354771015329086082181543134 : ((((((((p2 ∧ (p2 ∧ p5)) ∨ (True ∧ p4)) ∨ ((False → (False ∨ (p1 ∧ p2))) ∨ (p5 ∧ (p2 ∨ p4)))) → p1) → p2) ∨ p5) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213591456552435270229989293113 : ((((p1 → p3) ∧ True) ∨ p3) ∨ (((p1 ∨ (((p3 ∧ (p4 ∧ p5)) ∧ ((p2 ∧ p5) ∨ ((True ∧ (p2 ∧ p1)) → True))) ∧ p3)) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185235024674282970181622799454 : ((False ∧ ((False ∧ p3) → ((((p1 → p3) ∨ p1) ∨ False) ∨ p5))) ∨ (((p5 ∧ (p2 ∧ p1)) ∧ (((p5 ∨ p1) ∧ False) ∧ (p5 ∨ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53438200519500358139962578221 : (((((p2 ∧ p3) ∨ p1) ∧ (True → ((p2 ∨ p4) ∨ (True → True)))) → ((((p3 → p1) ∧ (p4 ∨ (True ∨ (False ∧ p1)))) → False) → p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : ((p3 → p1) ∧ (p4 ∨ (True ∨ (False ∧ p1)))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h9
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300359656887392512198616593235 : (False ∨ ((((p4 ∨ (p1 ∨ ((((p1 ∧ (p5 → (p5 ∨ p1))) → (False ∧ True)) ∨ p2) ∨ (False → False)))) → p5) ∨ True) ∨ ((True ∧ p5) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663738314386734325004480705757 : ((((p1 ∧ (p5 ∨ (False → (((((True → (False ∨ p3)) → (p3 ∨ (p5 ∧ False))) → p4) → (p1 ∨ (True ∧ p5))) → p3)))) → (p4 → p4)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47420839816668164918184862392 : (((p1 ∧ (((True ∨ (((p2 ∧ False) ∧ p2) ∧ False)) ∨ ((p4 ∨ (p5 → p2)) → (p4 ∧ (p2 ∨ p4)))) → (p2 ∨ False))) ∨ (p1 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352268369094585495973084637277 : (p4 → (((True ∨ (p5 ∨ p4)) ∨ p3) → ((((p5 ∧ p2) ∨ (p5 ∨ (p4 ∨ p1))) ∨ p2) ∨ ((p1 ∨ (p3 → ((p5 ∧ p5) ∧ p1))) ∨ p2)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49374203299733910346694073420 : (((p5 → ((p5 ∧ (((p4 → False) ∨ (False ∧ p4)) ∨ (p1 → (((True ∨ p5) ∨ (p5 ∧ True)) ∧ p3)))) → p4)) ∨ ((p2 ∧ p2) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68590758178296273801149586962 : ((p4 → ((p2 ∨ (((p2 → False) ∨ (((((True → p3) ∧ p5) → p3) → p3) → (p1 → ((p3 ∨ (p1 → p2)) → p4)))) → False)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119404940319699793303920349480 : ((p4 → (((p3 ∨ (p4 → p5)) → (((p3 ∨ (p3 ∨ (p5 → p2))) ∧ (False ∨ (False → (p1 → p2)))) ∨ (p1 → p1))) ∨ p1)) ∨ (p4 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748781136672672868038403179547 : ((((p4 → True) → (((((((False ∨ (True ∧ p3)) ∨ (p4 ∧ p3)) ∨ (True ∨ (p3 → False))) ∨ p1) ∧ p5) → ((False → p3) → p5)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687463152478419955537035961818 : (((((((p2 ∧ p3) → p3) ∨ (p5 ∨ ((p4 ∨ ((p5 → p5) ∧ p3)) ∨ True))) ∨ True) ∧ (((False ∨ ((p4 ∨ p3) ∨ False)) ∧ p2) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231729147885461594614387920900 : (((p2 ∧ p3) → p5) → (((p5 ∨ ((p5 → (((True ∨ p3) ∧ True) ∨ p2)) → True)) → ((p3 → False) → (p4 ∧ True))) ∨ (p4 ∨ (False → p1)))) := by
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
theorem thm_5_vars_150059097097336758803415588778 : ((True → (((p1 ∧ (p3 ∨ ((True → ((((p3 ∨ p5) ∧ p2) → p4) ∨ p2)) ∨ p4))) ∨ p4) ∧ (False ∨ p5))) ∨ (p5 → ((p1 → p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168759096005960256319871265099 : ((False ∨ (p2 → (p4 ∨ (p4 ∨ ((((p3 ∨ (p5 → (p1 → p4))) ∨ p4) ∧ p4) → p3))))) → ((p1 ∨ p5) ∨ ((p4 → p5) ∨ (p5 → True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174432669840750934790476896604 : ((((((False → p4) ∧ (p5 ∧ p2)) → p3) ∧ p3) → (((p5 ∧ p5) → p1) → False)) → (((p4 ∧ True) ∨ p2) → (p5 → ((p1 → p4) ∨ True)))) := by
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
theorem thm_5_vars_354654069822601216591959845438 : (p5 → (((((((((True ∧ p2) → (p3 → p2)) → p3) ∨ True) ∨ p2) ∧ (p3 ∨ p4)) ∨ (p1 → (p5 ∨ ((p2 → False) → p5)))) → p3) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197542096981032945055704169741 : ((((True ∧ (p1 ∨ p2)) ∨ p5) ∨ (False ∨ False)) ∨ (((p2 ∧ p4) ∧ (p3 ∨ p2)) ∨ ((p2 ∨ (p3 → True)) ∨ (True → ((p5 ∧ p4) → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_227363250175748864105281382014 : (((p3 → p4) → p2) ∨ ((((p1 ∧ (p3 → p4)) ∧ (True ∧ (p1 ∨ ((p4 ∨ p5) → p4)))) ∧ p1) ∨ (False → (True ∨ ((p5 ∧ True) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113560893151644992710355139140 : ((((True ∧ p4) ∨ ((False → (((True ∨ (((p2 → p1) ∨ ((p5 ∨ p2) → p2)) ∨ p4)) ∨ p1) ∧ p2)) → p2)) ∨ (p5 ∧ p1)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139452680746882674552968691702 : ((((((((False ∨ p1) ∨ p1) ∨ ((True ∨ p1) ∨ (((p2 ∨ p4) → p2) ∧ p3))) ∧ False) ∨ (p4 → p5)) ∨ p5) → False) → (p5 → (p5 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((((((False ∨ p1) ∨ p1) ∨ ((True ∨ p1) ∨ (((p2 ∨ p4) → p2) ∧ p3))) ∧ False) ∨ (p4 → p5)) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204814638149105332257715951905 : (((((p1 ∧ p2) → True) ∨ p4) → False) ∨ ((p5 ∨ ((p2 → (False ∨ (p1 ∨ True))) ∨ p5)) ∨ (p1 ∨ ((False ∧ (p5 ∧ True)) ∧ (False ∧ p3))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148436054028103150496423527852 : (((True ∨ (((((p3 → False) → p4) → (p1 ∨ (p4 → True))) ∧ p5) ∨ False)) → (((p2 → p4) → False) ∧ p5)) ∨ (False → ((p4 ∧ p5) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85284450508615428938951886693 : ((((((p2 → False) → ((p3 ∧ p2) ∧ (p4 → p5))) ∨ p5) ∧ p5) ∧ ((((((p2 ∨ p2) ∧ p5) → p1) → p5) ∨ False) → (True → False))) → p1) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (((((p2 ∨ p2) ∧ p5) → p1) → p5) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h7
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : (((((p2 ∨ p2) ∧ p5) → p1) → p5) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h15 := h3 h13
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h17 := h15 h16
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136508417540308882504553414626 : (((p2 ∧ (p3 → False)) ∧ ((p1 ∨ p1) ∧ ((((False ∧ p2) ∨ True) ∨ (p1 ∨ p4)) ∨ ((p2 → p4) ∧ (True ∨ False))))) ∨ ((False ∧ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150897331406891903735803111332 : (((((p5 → p5) ∨ p1) ∨ (False ∨ (p4 ∧ ((p5 → p3) → ((((p4 ∧ p4) ∧ True) → p3) ∧ p2))))) ∨ True) → (p2 ∨ (p1 ∨ (p2 → p2)))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h5
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111612069991289297097681761581 : (((((True ∧ ((p2 ∧ ((p5 → ((p3 → ((p5 ∨ (False → True)) ∨ p3)) ∨ True)) → (p1 ∨ p1))) ∨ True)) ∨ False) ∨ True) ∨ False) ∨ (False ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66721379260364438740294246740 : ((True → ((p1 ∨ p1) ∨ ((p2 → ((((True ∨ p4) → True) ∧ p1) ∨ (((p2 ∧ (p5 ∨ p3)) ∨ p3) ∨ True))) ∧ (p4 ∨ (p4 ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694825756144320053985094600258 : ((((p1 → ((False ∧ ((((p1 ∨ (p5 → p5)) ∧ p2) → p1) → True)) ∧ p1)) ∨ (True ∧ ((p5 ∧ ((True ∧ p4) ∧ (p1 ∨ False))) ∨ True))) ∨ p1) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593625742955170697889771456803 : ((((((p5 ∨ (((p3 ∨ p4) ∧ (((p1 ∨ p4) ∧ p4) ∧ ((False → p1) ∧ p3))) → p4)) ∧ p2) ∧ (False ∧ (p2 ∧ (True ∧ p1)))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258761525755711547227567688394 : ((True → False) → ((p3 ∨ ((False ∨ False) ∧ (True ∨ (p4 ∨ (p4 ∧ (((p2 ∧ p3) ∧ ((False ∧ (p5 → p1)) → p1)) ∨ (p2 → p2))))))) ∧ p5)) := by
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
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38181204951943509470330497349 : ((((p3 ∧ ((p1 → ((True → ((((p4 ∨ p2) ∨ (p2 → p2)) ∨ p2) ∧ p2)) ∨ (False → p5))) ∨ True)) ∨ ((True ∧ p5) ∧ p3)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55605142461274733449605428988 : (((False → (((p2 → p5) → p1) → p2)) → ((((p3 ∨ p1) ∨ (((p4 → (True ∧ p4)) ∨ p2) → False)) ∨ p3) → (p1 ∨ (p5 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183753674655131518070185155880 : ((p5 → (((False ∨ p5) ∧ p5) ∨ ((p2 ∨ (p4 ∧ p4)) → p4))) ∧ ((p5 → (p5 → (((((p4 → p3) ∧ p1) ∨ True) → False) ∧ p3))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46159078239483048336052127292 : (((((p3 → ((p1 ∨ (p5 → (False ∧ ((False → p4) ∨ (p2 ∧ p4))))) ∨ (False ∨ True))) → ((True → p4) ∨ True)) → p2) ∧ (p5 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309292609042814586281317589504 : (p2 ∨ ((p4 → (((p1 ∨ p5) ∨ ((True → (((False ∧ True) ∨ (True ∨ True)) ∧ p2)) → ((p3 ∧ False) ∧ (p5 ∧ True)))) ∨ p4)) ∧ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683661470766331731599329726826 : (((((((p1 → p5) ∨ False) → (p3 → (p1 ∨ (p2 → (((False ∧ p1) ∧ p1) ∧ p3))))) ∧ p5) ∨ (((p2 ∨ (True ∨ False)) ∨ False) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319139689555599037322613808837 : (p4 ∨ (((p5 → (p3 ∨ p3)) → ((p4 → p4) → (True → ((p5 ∨ (p2 ∧ (p3 ∨ p1))) ∨ True)))) ∧ (p3 → (p4 → ((p5 ∨ False) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110150090773649539511300261473 : ((p1 → (((True ∨ (p3 ∨ ((p5 → (True → ((True ∨ p2) ∧ (p4 ∨ False)))) ∨ (p4 → False)))) → False) ∨ ((p3 ∨ p1) → True))) ∧ (True ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55339549472460740317365650196 : (((True → ((p4 ∨ p5) ∧ (False ∧ p5))) ∨ ((False ∧ (((p2 ∨ (True → False)) ∧ (p3 → p5)) ∧ (False → p3))) ∨ ((False ∧ True) → True))) ∨ p3) := by
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
theorem thm_5_vars_750092458867207678277106182698 : (((True ∧ ((p4 ∧ ((((((p4 ∨ (p3 → (p2 ∧ ((True ∧ p1) ∨ (p3 ∨ p5))))) ∨ True) ∨ False) ∧ p1) ∧ p4) → (p2 → False))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179470638049508919873563074430 : ((True → ((((True → (((False ∨ p2) ∨ p4) ∨ p5)) ∨ p3) ∧ p5) ∨ p2)) ∨ ((((((p3 → False) ∧ False) ∨ (p2 ∨ p4)) → True) ∨ p4) ∨ p4)) := by
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
theorem thm_5_vars_346801032423751966276902024518 : (p3 → ((p2 ∨ (((p4 → ((True ∨ ((False ∧ p4) → (p3 ∧ p4))) ∧ (p5 → (True ∧ p3)))) → p4) → p5)) ∨ (p2 ∨ ((p4 ∧ False) ∨ p3)))) := by
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
theorem thm_5_vars_141510757847194935339075406314 : ((((p5 → p3) ∧ p3) ∨ (((True ∨ (False → False)) → ((p1 ∧ ((True → p5) ∧ p3)) ∧ False)) ∧ ((p2 ∧ True) → True))) → ((True → p4) ∨ p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : (True ∨ (False → False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165284111231536832559681351363 : (((((p1 ∨ p1) ∧ (p1 → ((False → p5) → p2))) ∨ ((p4 ∨ p2) ∧ p4)) → (False ∧ True)) ∨ (False → ((False ∨ ((p5 ∨ True) ∨ p5)) ∧ p3))) := by
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
theorem thm_5_vars_47869270185862538755627412605 : (((((p1 → (p2 ∧ ((False ∨ False) → p3))) ∧ (((p2 ∨ (p1 ∧ (p5 ∨ p2))) ∨ (p1 ∨ True)) ∧ p3)) ∧ (False ∨ p1)) → (p4 → p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h17 =>
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h19 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h18
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h20 := h5 h19
          -- We need to get the left conjuct of h20 based on <expert-advice>.
          let h21 := h20.left
          -- One of the premise coincides with the conclusion.
          exact h21
      case inr h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h23 =>
          -- False on the left can always be used.
          apply False.elim h23
        case inr h24 =>
          -- One of the premise coincides with the conclusion.
          exact h22
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h27 =>
        -- False on the left can always be used.
        apply False.elim h27
      case inr h28 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h29 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h28
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h30 := h5 h29
        -- We need to get the left conjuct of h30 based on <expert-advice>.
        let h31 := h30.left
        -- One of the premise coincides with the conclusion.
        exact h31
    case inr h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h33 =>
        -- False on the left can always be used.
        apply False.elim h33
      case inr h34 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h35 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h34
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h36 := h5 h35
        -- We need to get the left conjuct of h36 based on <expert-advice>.
        let h37 := h36.left
        -- One of the premise coincides with the conclusion.
        exact h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262466407245680538841956299162 : (True ∧ ((p3 ∨ ((((True → (True ∧ p3)) ∧ (p3 ∧ (False ∧ p1))) ∨ ((((False → ((p5 ∧ p5) ∧ True)) → p4) → p2) ∧ False)) ∨ True)) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117770324856272732726439414747 : ((p4 ∧ (((((p2 → ((p3 → p5) ∧ p5)) ∨ (p5 → (False ∨ ((p5 ∨ p3) → p1)))) → (False ∧ p3)) ∨ False) ∨ (False ∧ False))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668945863868624392104352532822 : (((((p3 ∨ ((((p4 ∧ p3) → p5) → p4) ∨ ((p4 ∨ (p3 ∧ (False ∧ ((True ∨ p1) ∨ p2)))) → p4))) ∨ p2) ∨ (False → (p2 → False))) ∨ p3) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628330800724956246149279103644 : ((((((p4 → p3) → (((p1 ∧ ((((p1 → p1) ∧ p3) ∨ (((p2 → p1) ∨ True) → p5)) → False)) ∨ (True ∨ p2)) → p3)) ∧ p4) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614204458744218886223436317897 : (((((((((True ∨ p4) ∨ (p5 ∨ (p1 ∧ False))) → p5) → (p1 ∧ (p1 ∧ ((p5 ∨ p5) ∨ p4)))) → p5) → ((p3 → False) ∧ p5)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_932036455873371650470606686791 : ((((((((p2 → p3) → p5) ∧ p3) → p5) → False) ∧ (((p3 ∨ ((p1 ∧ (((p5 ∨ p3) → p2) ∧ False)) ∧ p4)) ∧ False) → (p4 ∧ p1))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((((p2 → p3) → p5) ∧ p3) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : (p2 → p3) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h8
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h4
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197780680224895884213575970216 : (((p3 → (p5 ∨ True)) ∧ (p5 ∧ (p1 ∨ True))) ∨ ((p2 → (p5 → (False ∧ p1))) ∨ (p5 → ((((False → p3) ∧ False) ∧ (True ∨ p5)) → p3)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39049514772380256150753258358 : ((((p1 ∧ p1) ∨ ((p4 ∧ p5) ∧ (p2 → ((p4 → ((p4 ∨ ((True → p4) ∨ ((False ∨ p1) ∧ (p3 ∨ p2)))) → p3)) ∨ p2)))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64717681720908015520349715780 : ((p1 ∨ (p3 → ((p2 ∧ (p3 → p1)) ∨ (False ∨ ((p4 ∧ (p5 ∧ p2)) ∨ (((p1 ∧ ((True ∨ p1) → p2)) ∧ p5) ∨ (p4 ∨ p3))))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233061146826836694754215387770 : ((p4 ∧ (p2 ∨ p4)) → ((False ∨ ((False ∨ (p5 ∨ False)) → (p2 → False))) → (((((p4 ∨ p5) ∨ (p2 → p1)) → p3) ∨ p3) ∨ (p2 ∨ True)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



