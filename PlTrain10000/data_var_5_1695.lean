variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763637952993139449964801433273 : (((p3 ∧ (p5 ∧ ((p4 → p4) ∧ (((p3 ∧ p1) → ((((p2 → (p3 ∧ p2)) → False) ∧ (p1 ∧ True)) → p3)) ∧ (p2 ∧ (p1 ∨ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677554557163900213019330101168 : (((((p4 ∨ ((((p5 → (p4 ∨ ((False ∧ (False ∨ p5)) ∧ True))) ∧ False) → p5) → (True ∧ p4))) ∨ True) ∨ (((p2 → p5) ∧ p2) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690069026339311529547006505030 : ((((p5 ∧ (((((p2 → (p4 ∨ p2)) → (p5 ∨ (p5 ∧ True))) → p3) ∨ False) → p3)) ∨ (False ∨ (p1 → ((p4 → False) ∨ (p5 → True))))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51851521928889149740655156167 : ((((p2 ∧ (((False ∨ p4) ∧ (False ∨ (p4 → (p3 ∨ (p4 ∨ p4))))) ∨ p5)) ∧ p4) ∨ ((False → True) ∨ ((p2 ∧ p4) ∧ (p2 → True)))) ∨ False) := by
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
theorem thm_5_vars_679072099524170641200683679474 : ((((p1 ∨ ((p4 ∧ (p4 → (p4 → ((p2 → p5) ∧ ((p3 ∨ False) ∧ p2))))) ∧ ((p3 ∧ p5) ∨ p1))) ∨ (p4 ∨ (True ∨ (p3 → True)))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_172114355040234338016214708184 : ((((p2 ∧ (((p4 ∨ p3) ∧ p5) ∨ (p1 ∧ p4))) ∧ p1) ∧ (p3 ∧ (p5 ∨ p2))) ∨ (((p3 → p5) ∨ ((True → True) → (p1 → True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196733310803060898838909180554 : ((((p4 ∨ ((p3 → p3) → p5)) → p4) ∧ True) ∨ ((p2 ∨ ((p5 ∨ True) ∧ p1)) → ((p3 → ((False → p3) ∧ (p4 ∨ True))) ∨ (p3 ∨ p2)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111877807355507843667410614501 : ((((((p2 ∨ p2) → (((True → ((True ∨ p5) ∧ p3)) → p1) ∨ True)) ∨ (p2 ∨ p4)) → ((p4 → (p1 ∧ p4)) → p1)) ∨ False) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784383756292219894114865244404 : (((p3 ∨ (p3 ∧ ((p3 → ((p2 → p4) ∧ ((p1 ∨ True) ∨ p4))) ∧ (False ∨ (p2 ∨ (False → ((p1 ∧ p1) ∨ (p4 ∧ (p3 ∧ p2))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347032206883696509659362078904 : (p3 → ((((p2 ∧ ((p3 → (p2 ∨ (p1 → p1))) → (p3 ∧ (p3 ∧ p1)))) ∨ p1) ∧ p3) → (p3 ∧ ((False ∧ False) ∨ (p4 ∨ (p3 → p3)))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708888690792274493625929193634 : (((((((p5 → p2) → p2) ∧ False) ∨ (p1 ∨ p1)) → (((((((p4 ∨ True) ∧ p2) ∨ (False ∧ p5)) ∧ p5) → p4) ∨ p4) ∧ (p5 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339491068437169576457708683822 : (p1 → (False ∨ ((((False → p3) → (((False ∨ (True ∧ p2)) → ((((False ∧ p1) → p1) ∧ False) ∨ True)) → (p4 ∧ p3))) ∨ True) ∧ (p1 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783383765356284696155312835459 : (((p3 ∨ ((p3 ∧ (p4 ∧ (((p2 ∨ (p1 ∧ p5)) → ((True ∨ p3) → p2)) ∨ (p5 ∧ p1)))) ∨ ((p4 ∧ p2) ∧ (True ∨ (p3 ∨ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193952029707079865821147386886 : ((p2 ∨ ((p3 → True) ∧ (((p5 ∧ p3) → p4) ∧ p2))) → ((((p4 → (p5 ∨ (((p2 ∨ True) ∨ True) → (p1 ∨ p3)))) ∧ True) ∨ p2) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186284647783815513167191985728 : (((((False ∨ ((True ∧ p1) ∧ (p4 ∨ p4))) ∨ False) → True) → p5) → (((p2 → p2) ∧ (((p4 ∨ (False → (p4 ∧ p2))) ∧ p5) → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_24962695767691304992134721340 : (((False ∧ (p5 ∨ p3)) ∨ (((((p1 ∧ (p5 ∨ True)) ∨ p5) ∧ (p2 ∨ (True ∧ p3))) ∨ (p5 ∨ True)) ∨ (p2 → ((False ∨ p1) ∨ p2)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65945176705240686975450718214 : ((p4 ∨ (p2 ∨ (((((p2 ∨ (((p5 → (True ∨ (p3 ∧ p5))) ∨ (True ∧ p2)) ∨ (False ∨ p1))) → p2) → (p3 ∨ False)) → False) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112486212438411651520578904753 : ((((p3 ∧ (((True ∧ p2) → (p3 → ((p5 → p1) ∨ p3))) ∨ (False → (p2 ∨ (((p1 ∨ p3) → p1) ∨ p1))))) ∨ p2) → p4) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55716060722661879075655400589 : ((((p4 → (p3 ∨ False)) ∨ p1) ∧ (False ∧ (((p1 → p3) ∨ (((True ∨ (True → ((p3 → False) → p2))) → p2) ∨ p3)) → (p3 → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597977730812512033157458527068 : (((((p3 ∧ (False ∨ p1)) ∧ ((p1 ∨ ((((p1 → (p5 → p5)) ∨ (True ∨ p4)) → True) → (((p4 → p3) ∧ p2) → p5))) ∧ False)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709666901878066447616685675487 : ((((p4 ∨ ((p4 ∨ (p5 → p4)) → (p1 → p4))) → ((((p3 → p5) ∧ False) ∨ p5) ∨ ((p5 ∧ p2) → (True ∧ ((False ∧ p2) ∨ p5))))) ∨ p4) ∧ True) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114915905071852299143058065226 : ((((p1 ∨ (p5 ∨ (((p5 ∧ p1) ∨ p3) ∧ (p4 ∨ (p2 → p4))))) ∨ True) → ((p2 ∨ (p4 ∨ p4)) ∨ ((True → True) ∨ False))) ∨ (p3 ∧ False)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h14 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h14
          case inr h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h16
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h18 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h18
          case inr h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h20
            -- True on the right can always be proven directly.
            apply True.intro
  case inr h21 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h22
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187113200481912257544894736253 : (((p3 ∧ False) ∨ (False ∨ (True → ((p5 ∨ True) ∨ (p2 → p4))))) → (True ∧ (((p2 → True) → p5) ∨ (True ∧ (False → (p5 ∧ (p1 → True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41654350720374106923374007281 : (((((p4 → p5) ∨ ((p4 ∨ p4) ∧ p1)) ∧ (p4 → ((((False → p1) ∧ ((True ∧ False) ∨ p1)) ∧ ((p3 ∧ p4) ∨ p4)) ∨ p4))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213597315828143827303002651380 : ((((p3 → False) ∧ False) ∨ p4) ∨ (((p5 ∨ (p1 ∨ True)) ∧ (p4 ∨ (True ∧ ((True ∧ (p1 → True)) ∨ ((p4 ∧ (p1 ∨ p4)) ∨ p3))))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117067013424140281641495539724 : (((True → True) → (((True → ((p1 ∧ p4) ∨ p5)) ∨ p3) ∨ (((False → (p3 → False)) ∨ p3) ∨ (p1 ∧ ((False ∧ p5) ∨ p1))))) ∨ (p1 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192381555693378304996134869664 : (((((((p1 ∧ p4) ∧ p5) ∨ p2) → p4) ∧ p2) ∨ p1) → ((p1 ∨ p4) ∨ (p4 ∨ (((p5 → (p3 → p2)) ∨ ((True ∧ True) ∧ p2)) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (((p1 ∧ p4) ∧ p5) ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654019047028519688114416333040 : (((((p1 ∨ (((False ∨ p3) ∧ p3) ∧ (((True ∨ ((p4 ∨ p3) ∨ (((p2 → False) ∨ p1) ∧ p1))) ∧ False) ∨ p5))) ∧ p3) ∨ (p2 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349726486210048029550427664941 : (p4 → ((((False ∨ ((p1 ∧ p5) ∧ p4)) ∨ ((p1 ∨ p2) ∨ p3)) ∨ ((True ∧ (p2 → True)) → (((False → (p3 ∨ p1)) → False) → p2))) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : (False → (p3 ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h6
  -- False on the left can always be used.
  apply False.elim h8
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52180003654296515406927750736 : ((((True → (p3 → ((p4 → True) ∧ p1))) → (False → (False ∧ (p1 ∨ (p1 ∨ True))))) → (True ∧ ((True → (p4 ∧ False)) ∨ (p5 → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311310113427253215321829977368 : (p2 ∨ (True ∧ (p5 → ((((p2 ∨ (False → p1)) → False) ∨ (p1 ∨ (p2 ∧ (p1 ∧ (False → False))))) ∨ (((p5 ∧ (p2 ∨ True)) → p2) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318611951947792579471099898242 : (p4 ∨ ((((True ∧ p3) ∧ p4) ∧ ((((p3 ∨ ((p5 ∨ (p3 ∧ p1)) → p2)) ∨ False) ∨ ((False → p3) ∧ p5)) → (p4 ∧ p5))) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591672261861421997252625800024 : (((((((((((False ∨ ((((p3 ∨ p2) → False) ∨ False) ∧ True)) ∨ False) ∨ (False ∧ p1)) ∨ p3) ∨ p4) → p3) ∨ p2) ∨ (p1 ∧ p4)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167579311883467106548972738047 : ((((p4 → (p2 ∧ (p2 ∨ False))) ∨ (p1 ∨ (((p2 ∧ p1) → p4) → p4))) ∨ (False ∧ p2)) → ((False ∨ ((True → (p2 ∨ True)) → False)) → p5)) := by
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
    cases h1
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h7 : (True → (p2 ∨ True)) := by
          -- Implications on the right can always be decomposed.
          intro h8
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h9 := h4 h7
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h12 : (True → (p2 ∨ True)) := by
            -- Implications on the right can always be decomposed.
            intro h13
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h14 := h4 h12
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h16 : (True → (p2 ∨ True)) := by
            -- Implications on the right can always be decomposed.
            intro h17
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h18 := h4 h16
          -- False on the left can always be used.
          apply False.elim h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697382591978183934891816342112 : (((((p1 → p4) → (p5 → (p2 ∨ (p5 ∧ ((p2 ∧ p3) ∧ p2))))) ∧ ((False ∨ ((((p2 ∨ (False ∨ p1)) ∨ p3) ∨ False) ∧ p4)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205600573111280749287595555867 : (((p5 → True) ∧ (p3 → (p5 ∧ p5))) ∨ ((((False ∧ p2) ∧ p3) ∧ (p3 → ((p2 → (((False ∧ p5) ∨ p1) ∧ (True ∧ p3))) ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58733556229070007776426336370 : (((p3 → p3) ∧ ((((p3 ∧ ((True → p4) ∨ (p1 → p3))) ∧ ((True → p5) → p2)) → (p4 → p4)) ∨ ((p3 ∨ p4) → (False ∧ p2)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304701607955054059634248390882 : (p1 ∨ ((((p5 ∧ True) ∧ (((p3 ∧ p3) ∨ False) ∧ ((((p1 ∧ p1) → (False ∧ False)) ∨ p4) → ((p5 ∧ p5) → p4)))) → p4) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228139184648335763634514016006 : ((p4 ∧ (p2 → p2)) ∨ (((p2 ∨ ((p5 ∨ p4) ∨ (((p2 ∨ False) ∧ (p1 → p5)) → ((p5 ∨ p3) ∨ p2)))) ∨ False) ∨ ((True ∧ p2) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762760039388695225912995850883 : (((p3 ∧ (((True ∧ ((p3 ∧ p4) → (True ∧ (p1 → p5)))) ∨ False) → (p1 ∧ (p4 ∨ (((True ∧ p2) ∧ False) → (p4 → (True ∨ True))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166523538718290613650586458974 : ((p4 ∨ ((True ∨ False) ∧ (p3 ∧ (p1 → (p2 → ((p4 ∨ (True ∧ (False ∨ False))) ∨ False)))))) ∨ ((((False ∧ p4) ∧ p4) ∧ (p1 ∧ p4)) → p2)) := by
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
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219015589929257921010450733489 : ((p4 ∧ (p3 → (False → p2))) → (p5 ∨ (p4 ∧ ((p1 ∨ (p1 → (p4 ∧ ((((p3 ∨ p3) → p5) ∧ (p5 → (p4 → False))) ∨ p4)))) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54689713336033204015191034066 : ((((p3 ∨ (((p4 → False) ∨ p1) ∧ p5)) → p1) → (((((p3 → False) ∨ (p5 ∧ ((p1 → False) ∨ p4))) ∧ p2) ∨ p1) ∧ (p2 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752204157777837889459901735316 : (((True ∧ (p3 → ((((False ∧ p3) ∨ True) ∨ p5) → ((((p3 → ((p1 → p1) ∧ p1)) → ((p1 → p1) → p4)) ∧ (p2 ∨ True)) ∨ p3)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219565822502557662404007786366 : ((True → ((p4 ∨ p3) ∨ p2)) → (((((p1 ∨ (p2 ∨ p2)) ∨ p3) ∧ (p3 ∨ (p3 ∨ ((p4 → p3) ∨ (False ∨ p4))))) ∧ (p3 ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102726509717276070206916734573 : (((((p1 ∨ False) → ((p3 ∨ ((p1 ∨ (p1 ∧ (False ∨ p5))) ∧ ((p2 → p4) → (p5 ∧ p4)))) → (True → p2))) ∨ p1) ∨ True) ∧ (True ∨ p5)) := by
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
theorem thm_5_vars_605046809822314620374578251238 : ((((p2 → ((((True ∧ ((p4 ∧ True) ∧ (True ∧ (((True ∨ p5) → p1) → ((p5 ∨ p2) ∨ p5))))) ∧ p4) ∨ (p1 ∧ p2)) ∨ p5)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52316908647309779853850046556 : (((((((False ∧ (p5 → (False ∨ p4))) → p5) ∨ p1) ∧ (p4 ∨ p3)) ∨ False) ∧ ((p3 → ((p2 ∨ ((p1 ∨ False) ∧ p5)) ∧ False)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194281455592295466330941251368 : ((p5 → (p3 ∧ ((((p2 → p5) ∨ p1) → p5) ∧ p2))) → (((((p3 → p5) ∧ (p4 ∧ True)) ∧ p3) ∨ (p2 ∨ ((False ∨ p2) ∨ p5))) → p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h10 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h11 := h6 h10
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h12 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h13 := h1 h12
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- One of the premise coincides with the conclusion.
      exact h17
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
          -- One of the premise coincides with the conclusion.
          exact h21
      case inr h22 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h23 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h24 := h1 h23
        -- We need to get the right conjuct of h24 based on <expert-advice>.
        let h25 := h24.right
        -- We need to get the right conjuct of h25 based on <expert-advice>.
        let h26 := h25.right
        -- One of the premise coincides with the conclusion.
        exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49208285476975478046468674783 : ((((True ∨ (p5 ∨ p5)) → (((p3 → (p4 → p4)) → (p3 ∨ ((p5 → True) → ((p2 ∨ p5) → False)))) ∨ p1)) ∨ (False → (True ∧ False))) ∨ p5) := by
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
theorem thm_5_vars_668826236803739732825628569069 : ((((((((p5 ∧ (p5 ∨ p4)) ∨ p4) → (p1 ∨ (p1 → True))) → (p5 → (((p4 ∨ p5) ∧ p5) ∧ False))) ∨ p2) ∨ ((p3 ∧ p2) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321526464052561751539296930335 : (p4 ∨ (p1 → (p3 → ((p5 ∨ p4) ∨ ((p4 ∨ ((False → (p5 → (p1 ∧ False))) → (((p4 ∨ (False → p4)) ∨ p4) ∧ p3))) ∨ (p5 ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344822502116562345640797031055 : (p2 → (p4 → (p1 → (p2 → (False ∨ (((True → ((p5 ∧ ((p1 ∨ p2) ∨ (p5 ∨ ((False → False) ∨ (p1 ∨ p1))))) ∨ p3)) ∨ False) ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682579220363212099492434399628 : ((((((True → (p5 → (False ∨ (p4 ∧ p5)))) ∨ p4) ∧ (True ∧ (((p1 ∨ True) ∧ False) ∨ p5))) ∧ (p2 ∨ ((p4 ∧ (p1 → True)) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47105917794497423090643722833 : ((((p1 ∧ (((True ∨ False) ∨ (((True ∨ False) ∧ p4) ∨ True)) → (((p4 ∧ True) ∨ p4) ∨ True))) ∧ ((p5 → False) ∧ p2)) ∨ (p2 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68175779077803940111407693036 : ((p3 → (((((((False ∨ ((False → (True → p5)) → False)) ∧ p1) ∨ (True ∧ ((True → p1) ∧ p1))) → (p5 ∧ p1)) → p5) ∨ p4) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205054528971364082267694376716 : (((p1 → ((p3 → False) → p5)) → False) ∨ ((p3 ∨ ((p3 ∨ p4) ∨ ((True → (False ∧ (((p3 ∧ True) ∨ (p2 ∧ False)) ∧ p3))) ∨ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336469862395639390342500543662 : (p1 → ((p2 → ((((False ∧ (((p4 ∨ p2) → (p4 ∧ p2)) ∧ (((False ∧ p2) ∨ (p1 ∨ False)) ∨ p2))) → p2) → False) ∨ (p2 → p2))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42582155800281602069967479100 : (((p2 ∨ (((((p5 → True) ∨ (p2 → (p3 → False))) → p5) ∨ (p4 ∨ (p1 → p4))) ∨ ((False → p2) ∨ ((p5 ∨ p4) ∧ p2)))) ∨ p5) ∨ p1) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161824211840361170475777746155 : ((True → (((((((p3 → (p1 ∨ p4)) ∧ p1) ∧ p4) ∧ ((p2 ∨ p3) ∨ p4)) ∧ p4) ∧ False) ∧ p2)) → ((p4 → False) ∨ (p4 ∧ (p5 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50969762962469759662700665350 : ((((((True → p2) ∨ True) ∧ p5) → (True ∧ (p1 → ((p4 ∧ ((False → False) → p4)) ∨ p5)))) ∧ ((((False ∨ True) → False) ∨ False) → p4)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
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
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137156146444239704324661245232 : ((False ∧ (((((p5 ∨ (p4 ∧ p2)) ∨ p4) ∧ ((p4 ∨ p4) ∧ p5)) ∨ ((True ∨ (p4 ∧ (p4 ∨ p4))) ∨ p5)) ∨ p2)) ∨ (p5 → (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46999348110805945948078774892 : (((((p5 ∧ ((p4 → p2) → p1)) → ((p4 → (p3 ∧ p1)) ∨ ((((False ∧ False) ∧ True) ∨ (p1 ∨ True)) ∨ True))) → p5) ∨ (p5 → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261639152539980126128588162595 : ((p5 → p5) → (((p2 ∨ ((((p3 ∨ (p4 → p4)) ∧ (p2 ∨ False)) ∨ p3) → p5)) ∨ True) ∨ ((((p3 ∨ p3) ∨ p1) ∧ (p5 → True)) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350921739279105003341930360057 : (p4 → ((((p4 ∨ False) → ((p4 → p1) ∨ ((p1 → (((p5 → (p2 → p1)) ∧ (p4 ∨ p5)) ∧ (p1 ∨ p3))) ∧ p5))) ∨ p4) ∨ (False → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193683362579806245453477787712 : ((p1 ∧ ((p4 ∧ (p4 ∧ (p3 ∧ (False ∨ True)))) → p5)) → (((p2 ∧ ((p4 ∧ (p3 ∧ (p3 ∧ (False ∨ False)))) ∧ p5)) ∨ p5) ∨ (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327501915514733608285281997232 : (True → ((((False ∧ False) → p5) ∧ (p5 ∧ ((((p4 ∨ (p3 ∨ ((p2 ∧ p5) → ((p5 ∧ p1) → p5)))) → True) ∨ (p3 → p3)) ∧ True))) → p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308742927111759439306649035819 : (p2 ∨ ((p4 → ((p5 ∨ (p1 ∨ ((p3 ∨ ((p4 → p1) → (p1 → p2))) ∧ ((p2 → (p1 → (True ∧ p5))) → False)))) ∨ (p1 → True))) ∨ p4)) := by
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
theorem thm_5_vars_171467007376845211705401457135 : (((p1 ∨ (((((p3 → p5) → True) → (p2 → (p1 → False))) → p2) → p1)) ∧ p1) ∨ ((p1 ∨ ((p2 ∧ ((p5 ∨ p1) ∨ True)) → p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56233096629717446900460734476 : (((p4 ∨ (p2 ∨ (True → p1))) ∨ ((p2 ∨ (((p4 ∧ (p2 ∨ ((True → (p2 ∧ (p2 ∧ False))) ∧ p5))) → p2) ∨ False)) → (p2 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134805364504562445326628364491 : (((p5 ∧ (((False ∧ ((((False → ((False ∧ p5) ∧ True)) ∨ p2) ∨ ((False ∧ p4) ∧ True)) ∧ p4)) → p3) ∧ p1)) → p4) ∨ (p2 → (p5 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52633607933789791878773355291 : ((((True ∧ p2) ∨ (((p4 → True) ∧ ((True ∧ p3) ∨ (p2 → False))) → False)) ∨ (p1 → (False → ((False ∧ (False ∨ (p5 ∨ False))) ∨ False)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164460852125076501670412653224 : ((((True → (p3 ∧ (False ∨ ((p4 → p1) → (((True ∧ p4) → p2) ∨ False))))) ∧ p4) ∧ p3) ∨ (((p1 ∨ (False ∧ True)) → (False ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157874599552883511977598499973 : ((((p2 ∧ (True → (((p4 → p5) ∨ True) → p3))) → p5) ∨ ((p3 ∨ ((p3 ∨ p4) ∨ False)) → p2)) ∨ (((p3 ∧ p2) → (p4 ∨ True)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_53142497234753169036271593248 : ((((p4 ∨ ((False ∧ (False ∨ True)) ∨ (False ∨ (p3 ∨ p3)))) ∧ p1) ∨ (False ∧ (p3 ∨ (((True → p5) → True) → ((p3 ∧ p5) → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734131477706924192723130620107 : ((((True ∨ p5) ∧ ((((((True → True) → (p5 → True)) → (p1 ∨ p5)) ∧ p2) ∧ (p3 → ((p1 ∨ (p4 ∨ (p4 ∨ p1))) → p1))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172540546954562662247403135813 : ((((False ∨ p3) ∧ True) ∨ (((False → p5) → (p3 ∨ p1)) ∨ (p4 ∧ (p1 ∨ p1)))) ∨ (((((p5 ∨ True) ∧ False) ∧ (p2 → False)) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67661274727739124654935470437 : ((p1 → (p4 ∨ (p5 ∨ ((((p4 ∧ ((p4 ∧ p4) → True)) ∧ True) ∨ p2) ∨ ((p4 ∨ ((((False → p3) ∨ p3) ∨ p3) → p4)) ∨ p1))))) ∨ False) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117152200277832513347130882138 : ((True ∧ ((p5 ∧ (((True ∧ p2) ∧ p4) ∨ (((False ∨ (((p3 ∨ p5) ∨ (p4 ∧ True)) ∧ (p3 ∨ p5))) → p2) ∧ False))) ∧ p5)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785825568265590696395146841365 : (((p4 ∨ ((p3 ∨ (p4 ∨ (((p5 ∨ p5) ∨ (((p3 ∧ (p3 → (p4 ∧ (True → False)))) ∨ p4) → p1)) ∨ ((p5 → False) ∧ p1)))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67699209372919150314099730849 : ((p1 → (p4 → ((p3 ∧ p1) ∧ (((p3 ∧ (p3 ∨ ((((p4 → p3) ∧ p3) ∧ p5) ∨ p4))) → (p3 ∨ p4)) → (False ∨ (p3 ∨ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310630954480317395199946324366 : (p2 ∨ (((False → p2) → (p4 ∧ True)) ∨ (((((p2 → (True ∨ True)) ∨ ((p3 → p2) ∧ p3)) → p3) ∨ (p4 → False)) ∨ (p5 → (p4 ∨ p5))))) := by
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
theorem thm_5_vars_135279475635081697130143922542 : (((True → (((p4 ∨ (p3 ∧ ((p1 ∧ p5) → p4))) ∧ True) ∧ (((p3 ∧ True) ∧ (True ∨ p2)) ∧ False))) → (p4 → False)) ∨ ((False → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46714648690934409648258324025 : (((p5 ∨ ((False → (((((((False → False) ∨ True) → p5) ∨ p2) → p3) ∧ (p3 ∧ p4)) ∧ ((p4 → p2) ∨ p1))) → p2)) ∧ (p1 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307363812959683967795557243549 : (p1 ∨ (p4 ∨ ((((((p4 ∧ (p1 → (True ∧ p2))) → (p2 ∧ True)) → p3) ∧ p2) ∨ (((p5 ∨ p2) ∧ (p2 → p3)) → (True ∨ p2))) ∨ p1))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193088098158292595149873633698 : ((((True → p2) → (False ∧ False)) ∧ ((p4 ∨ p3) ∨ True)) → ((p5 ∨ p2) ∨ ((True ∨ (p4 ∨ p5)) ∧ (p2 → (p4 → ((p2 ∨ p5) ∧ p3)))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : (True → p2) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h8
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h16
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h16
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h18 : (True → p2) := by
      -- Implications on the right can always be decomposed.
      intro h19
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h20 := h2 h18
    -- We need to get the left conjuct of h20 based on <expert-advice>.
    let h21 := h20.left
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248707024093063432055209667622 : ((p3 ∨ p2) ∨ ((p4 ∧ ((((p1 ∨ p1) → p5) → (p5 ∧ p5)) ∨ p4)) → ((p5 ∨ p1) → (((False ∧ (p1 ∨ False)) ∨ p1) ∨ (p3 → p4))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671807551290644171997261905685 : ((((((p5 → (True ∧ p3)) → ((p2 ∨ ((True → True) ∨ (((True → p4) ∨ p1) → (p4 ∧ p1)))) ∨ p1)) ∧ p2) → ((p3 ∨ p4) ∨ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216047387393039894829190120659 : ((p5 ∨ (p1 ∧ (p3 ∨ False))) ∨ (p5 → ((True ∧ (p1 ∨ (((p1 ∨ (True ∧ False)) ∨ True) ∨ False))) ∧ (p5 ∨ (p1 ∨ (p1 ∨ (p4 → p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119574754801172495995996920185 : ((p5 → (((p4 → p1) ∨ (p5 ∧ True)) → ((p1 ∨ p1) ∧ (False ∨ ((((p3 ∧ (False ∨ p2)) ∧ False) ∧ p3) ∨ (p4 → False)))))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45889045236374291983849617653 : (((p3 → (p2 ∨ ((p4 ∨ p1) ∨ (p3 ∧ ((((((p5 ∧ True) ∧ (p3 → False)) ∧ p2) ∨ (p2 ∨ True)) → False) ∧ (True → False)))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110814556243446689780885682965 : (((((((False → (p1 ∨ p4)) ∧ p3) → p1) ∨ ((True → p4) ∧ (((False → p3) → (p1 ∨ True)) ∧ (p3 ∨ p5)))) ∨ p5) ∧ p2) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191252657330538317612296849259 : (((p2 ∧ p4) ∧ ((p2 → ((p5 ∧ p1) ∧ False)) → p2)) ∨ ((p3 ∧ (((p4 ∨ p3) → (p2 ∧ ((True → p2) ∧ p5))) ∧ p1)) → (True ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204592076850258114200168654787 : ((((p2 ∨ p2) ∨ (p2 ∧ False)) ∨ p2) ∨ (p1 → (False → ((p3 ∧ False) ∧ (((p2 → (p1 → True)) → True) ∨ ((p3 → False) ∨ (p5 → p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158403834866698383808349179192 : (((True ∧ p2) ∨ (((((p4 ∧ False) ∨ p5) ∨ (p4 ∨ (True ∨ p3))) ∧ (True ∧ (p1 ∧ True))) ∧ True)) ∨ ((p3 ∨ False) → (True ∨ (p1 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307710379003784850004929526014 : (p1 ∨ (p2 → (p1 ∨ ((((((False ∧ (False ∧ (p5 ∨ (p4 → (p1 ∧ p1))))) ∨ True) ∨ p3) ∧ p2) ∨ (p4 ∨ ((p1 ∧ p3) ∧ p2))) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354610998467969525574546453794 : (p5 → ((((False ∨ (((True ∨ (True ∨ (p4 → (((p4 → (False → p3)) ∨ p1) ∨ (p3 ∧ p4))))) ∨ p3) → p4)) → (p2 ∧ p1)) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219823335245425506669934765160 : ((p3 → ((p5 → p1) ∧ True)) → ((p1 → p5) ∨ (((False ∨ ((p4 ∧ False) ∨ False)) ∨ (((p1 ∨ (False → p5)) → p3) → True)) ∨ (p4 → p2)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61538362016538908260326669102 : ((p1 ∧ ((((p3 ∨ p3) ∨ p1) ∧ ((p2 → p2) ∧ ((False ∨ p2) ∨ p4))) ∨ ((p2 → False) → ((((False → p3) ∧ p2) ∧ p4) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590670624244811384852949230608 : (((((p4 ∧ (((False → ((p3 ∨ (p3 ∧ p4)) → (p1 ∨ False))) ∧ ((p2 ∧ p1) → p2)) ∨ ((p2 ∨ p4) ∨ (False → p1)))) → p3) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



