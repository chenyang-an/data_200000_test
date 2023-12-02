variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147387073707490715089718713131 : ((((((False ∨ False) ∧ (False ∨ (p4 ∧ p4))) ∨ p2) ∧ (True ∨ ((p1 ∨ (p5 ∧ p2)) ∧ (True ∨ p1)))) ∨ p3) ∨ ((p2 ∨ p4) → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49943893783296112174119811826 : ((((p4 → ((p3 ∧ (((False → (True ∧ p3)) ∨ False) ∨ ((p1 ∨ False) → p4))) ∨ p2)) ∧ (p4 ∧ p4)) ∧ (p4 ∨ (p2 ∧ (p2 → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162406493008649510138719857971 : (((((p5 ∨ p2) ∧ (p3 ∨ (p4 ∧ ((p4 ∨ p4) ∧ p1)))) ∨ (p4 ∨ (False ∧ p1))) ∨ True) ∧ ((((p1 ∨ True) ∧ True) → True) → (p2 ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65000455937909580243217973898 : ((p2 ∨ (((p4 ∨ p3) ∨ True) → ((False ∨ (p2 ∧ (p5 ∨ (p1 → p4)))) → (((((p3 ∧ True) → True) → p2) → p1) ∨ (p2 ∨ p5))))) ∨ False) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339756174851935932805760396752 : (p1 → (p4 ∨ ((p1 ∧ p1) ∧ ((p2 → (((((p4 ∨ True) → p4) ∨ p4) → p2) → (False ∨ ((p5 → ((p2 ∨ p1) → p3)) ∧ p5)))) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798616020803943137715560115825 : (((p1 → (((p3 ∨ (p1 ∧ p4)) → (p4 ∨ True)) → ((p1 → ((True → ((p4 → (p5 ∧ p3)) ∨ True)) ∧ (False → (p3 → p4)))) ∨ p1))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52965059153410645224278463945 : ((((((False ∧ p2) → (p1 ∧ (False → (p5 → p3)))) ∨ p1) → p2) ∧ ((p5 ∧ p4) ∧ (p4 ∨ (p2 → (p1 ∧ (p4 ∧ (p2 ∧ p4))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322373493120496108666384850461 : (p5 ∨ ((((p4 ∨ True) ∧ (((((p5 ∨ ((p4 ∧ p3) ∧ p1)) → p2) ∧ p5) ∨ p2) ∨ (p3 ∧ p2))) ∨ (p1 → ((p3 → p4) ∨ p1))) ∨ p4)) := by
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
theorem thm_5_vars_649821666200816427451484102626 : (((((p4 ∧ ((((True ∨ p3) → False) ∧ p4) ∧ ((((p3 → (p4 ∧ p1)) ∨ (p5 ∨ p3)) → p3) → False))) → (True → p1)) ∧ (True ∨ p2)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h9
  -- False on the left can always be used.
  apply False.elim h10
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781221441811889882494873082236 : (((p2 ∨ ((p3 → p3) → ((p5 → ((p2 → p1) ∧ (True ∧ (p1 ∨ (p3 → p5))))) ∨ ((True → (((p5 ∨ p2) → p4) ∨ p2)) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731238865772897082368236489440 : ((((p3 ∨ (p4 ∨ p1)) → (False ∧ (((False ∨ p3) ∧ (((p4 ∨ p5) ∧ (((p2 ∨ p5) ∧ False) → True)) ∨ p2)) ∨ ((p1 ∨ True) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54351143214063476996646879252 : (((p1 ∨ (p2 → (((True ∧ False) → p1) → False))) ∧ (((((False ∨ p3) → p4) ∧ p3) ∧ p3) → (p5 → ((True ∧ (p2 ∧ p4)) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53903342071528258448225930425 : (((p4 ∧ ((((p5 ∨ (p3 ∧ p3)) → p3) → p2) ∨ p5)) ∨ ((p4 ∨ ((p4 → True) ∧ ((p3 ∨ (p1 ∨ (p3 ∧ False))) → p2))) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112091571656801634153084069254 : ((((p1 → p5) ∨ (((((p2 ∧ p4) ∧ p1) ∧ False) → p4) → ((False ∧ p5) ∧ (True ∧ (False → ((True → p5) ∧ p5)))))) ∨ p1) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135141418797897055872360811933 : (((p2 ∨ ((((p5 → (p1 ∧ True)) ∨ (p3 ∧ p1)) ∨ (p4 ∧ (p3 ∧ p3))) ∨ (p5 ∨ (p2 ∧ p5)))) ∨ (p2 → p1)) ∨ (p2 → (p2 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42895135299099644188631056483 : (((p3 → ((p4 ∧ (((p1 ∨ p1) ∨ p2) → ((p5 ∧ ((p4 → p5) → ((p4 ∨ p3) → p4))) → False))) → (False ∧ (p5 → p3)))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112486766915203430830138357436 : ((((p4 ∧ (((p4 ∨ (((p2 ∨ ((p2 → False) ∨ (p5 → p4))) → (p5 ∨ False)) ∨ p4)) → (p2 ∧ p2)) ∧ p5)) ∨ p4) → False) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347990911673968105427993019160 : (p3 → ((p4 → p4) ∧ (((True ∧ (p1 → (((p2 ∨ (p5 ∧ p4)) ∧ (p2 ∧ False)) ∨ True))) ∨ (((p1 → False) ∧ (False ∨ False)) → p4)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324172066350721073568357984410 : (p5 ∨ (((False ∧ (p4 → p2)) ∧ (p2 → ((p5 → p3) → p3))) ∨ ((False ∨ True) → ((p5 ∨ True) ∨ ((p5 ∨ (p1 → p5)) ∨ (False → False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_634846036776034524869345593088 : (((((((True ∨ p5) ∨ p4) → (p3 ∧ ((False ∨ p4) → (p1 ∨ ((p4 → ((p4 ∧ True) ∧ p5)) → p2))))) ∨ ((True ∧ p1) ∨ True)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785081811727235636601538334854 : (((p4 ∨ (((True → (p5 → (((True ∧ ((p5 → p1) → (p3 ∨ ((((p5 ∨ True) ∧ p3) ∧ True) ∧ True)))) ∨ p2) → p4))) ∨ p3) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264755793040545878904361882318 : (True ∧ ((p1 → True) ∧ (p5 ∨ (p4 ∨ (((((p1 ∨ (p4 ∨ (p3 → p5))) ∨ True) ∧ (p4 → (p2 ∨ True))) ∨ (p5 ∨ (False ∨ False))) ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192081908371505309926874546241 : ((p3 → (p3 → (p5 ∨ (((False → p1) → False) ∨ p5)))) ∨ (p1 → ((False → p2) ∨ (((False ∧ (((p1 → p4) ∧ p1) → p5)) ∨ True) → p2)))) := by
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
theorem thm_5_vars_204236225614642308053346777586 : ((((p2 ∧ p3) ∧ (p4 → p4)) ∧ False) ∨ ((p4 ∧ (p4 ∧ ((((p2 ∨ (p4 ∧ False)) ∧ (p3 ∨ False)) ∨ ((p2 → p4) ∧ p1)) ∧ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172075710841598872696457259309 : ((((((p3 → p5) ∧ (False ∨ False)) → False) ∨ ((False ∧ p1) ∧ p1)) → (p2 ∧ p3)) ∨ (p4 → ((((False → (p5 → p4)) ∧ p4) ∧ p4) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69272043619058010174622106530 : ((p5 → ((p1 ∨ p1) ∨ (((p3 → p5) → False) ∨ ((True → True) ∧ ((p2 ∧ (((p2 → True) ∧ ((p4 ∨ p3) ∧ p1)) → p4)) ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230968368313698257395752435384 : (((p4 ∧ p1) ∨ p3) → (((((p2 ∨ (((True → (False ∧ (p3 ∧ p5))) ∨ p5) ∨ p3)) ∧ p3) ∨ p2) ∨ ((False → p5) → True)) ∨ (p1 ∨ p1))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656087306410838105421604968597 : (((((p1 → (p4 ∨ (p1 ∨ ((((False → ((False → False) ∨ p5)) ∧ p3) ∨ p1) → p4)))) → (((p5 → True) → p4) → p1)) ∨ (True ∨ False)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_2189496289941391838456615735 : (((((p3 ∧ True) ∧ (p4 → (p5 → p2))) → p4) → ((True ∧ p2) ∧ (p4 ∨ p5))) ∨ ((p3 ∨ True) ∨ ((p3 ∨ (p2 ∨ p4)) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50530092313223104687577323565 : (((((((True ∨ p4) ∧ (p2 ∧ ((p3 ∧ p2) ∧ (((p2 → p3) ∨ p1) ∧ p2)))) ∧ p5) ∨ p5) ∨ p5) → (False ∧ (False → (p3 ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339865419949890041133432881552 : (p1 → (True → ((p5 ∧ (((False ∨ p3) ∨ p4) → (((True ∧ (p3 ∨ p5)) ∨ (p2 ∧ False)) ∧ False))) ∨ (((p5 ∨ p5) ∧ False) → (False ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305720880385787671451846991238 : (p1 ∨ ((p5 ∨ ((p2 → (p4 ∨ (p2 ∨ (p4 ∧ p5)))) ∧ p5)) → ((((p1 ∧ False) → p5) → p4) ∨ (True ∧ (((p3 → True) → p5) ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183962957130292445773880669875 : (((p1 → ((True ∨ (((p1 ∧ False) → p5) ∧ p3)) → p2)) ∧ p2) ∨ (((p4 ∨ ((p5 ∨ False) ∨ ((p5 ∧ p3) → p1))) ∨ p4) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135620049220980661513333456444 : (((p1 → ((((False ∨ (p2 ∨ (p5 ∧ p2))) ∨ (False ∧ p2)) ∨ p2) → (False ∧ p5))) ∨ (p3 → ((p1 → False) ∨ True))) ∨ (False ∨ (p2 ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148552021441022982112438559016 : ((((((p2 ∧ p4) → (p1 ∨ False)) ∨ (False ∨ p2)) → p3) ∧ ((p2 ∨ (p4 → True)) → (True → (p2 ∨ p2)))) ∨ ((p3 ∧ (p1 ∧ p5)) → p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338238179663460833525563190751 : (p1 → ((((False ∨ p5) → True) → (p2 ∨ p2)) ∨ ((((False → p2) ∧ (p2 ∧ p1)) ∧ (False ∧ (True ∧ ((p1 ∧ p3) ∧ False)))) → (p5 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h4.left
  let h10 := h4.right
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h14.left
  let h16 := h14.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h12.left
  let h18 := h12.right
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205128785114620800349078881131 : ((((p1 ∧ p1) → p4) ∧ (p2 ∧ p2)) ∨ (((((p2 → p3) → (((p2 ∨ False) ∧ p1) ∨ p2)) ∨ (True ∨ p5)) ∧ True) ∧ ((p4 ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764255371361547367252533945075 : (((p4 ∧ ((((True ∧ (p1 → (((((((p2 → p3) ∧ p3) ∨ p3) ∧ p3) → p1) ∧ (p1 → p1)) ∨ (p1 ∨ p1)))) ∧ p1) → False) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131593794542422997839189033730 : ((((p2 ∧ p1) ∨ p4) ∨ (((True ∨ p2) → p1) → ((p5 → ((p4 → p4) ∧ ((p2 ∧ (p3 ∨ p4)) ∨ p3))) ∨ p1))) ∧ ((p2 ∧ False) → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201751301405186538190267175779 : ((((p3 ∧ (p5 ∧ p1)) ∨ p4) ∨ True) ∧ (True → ((True ∨ p3) ∧ (p1 → (((False ∨ (p4 → False)) → p3) → ((p3 → (p4 ∨ True)) ∧ True)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64372214627558904136759631083 : ((p1 ∨ (((p4 ∨ p4) ∨ ((p2 ∨ (True → (p1 ∧ (p3 ∨ (((p5 ∨ (True → p4)) ∨ (p5 ∧ p2)) ∨ (p3 ∧ p4)))))) ∨ p4)) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166266095545881457650424920171 : ((p3 ∧ ((True → False) → (((False ∧ p2) ∧ p5) ∧ (((p3 → (p1 → True)) → p1) ∨ False)))) ∨ ((p4 ∨ True) ∨ ((p3 ∧ False) → (p1 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148109492601336621700207020614 : ((((True ∧ (((p4 ∧ (p1 → (p5 → p2))) ∨ p4) ∧ p3)) ∧ (((p1 ∨ False) ∧ False) → p2)) → (p2 ∨ p3)) ∨ ((True ∧ True) ∨ (p2 ∧ False))) := by
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
theorem thm_5_vars_151072776722545444944630361019 : ((((((p1 → (((True ∨ p5) → p3) → p4)) → p1) ∨ ((False ∨ (p5 ∨ p2)) ∨ (p3 ∨ p2))) ∨ p3) → p1) → (p4 ∨ (p5 → (p4 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58475329193858788228019531140 : (((p4 ∨ True) ∧ (((p1 → (((p2 ∨ p1) ∧ (p2 ∨ p2)) ∧ p5)) ∧ p1) ∨ ((True ∧ (((p3 ∧ p2) ∧ (p5 ∧ p5)) → p2)) ∨ p5))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690295611641114220411610744209 : ((((p1 → ((p4 ∧ (((p2 ∧ ((True ∧ p5) ∧ False)) ∧ p5) → p4)) → (True ∧ p5))) ∨ ((p2 → (((False ∧ p3) ∨ p5) ∧ False)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116616628108539425793489327607 : (((False → False) ∧ (((False ∧ (p2 ∨ (False ∧ ((p5 → False) ∧ p5)))) ∨ p5) ∨ (((p2 ∧ p3) → (True ∨ p3)) ∨ (p5 ∧ True)))) ∨ (p1 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147162930111840551493724986763 : (((p5 ∧ (((p2 → ((((p5 ∧ p1) → False) ∧ p5) ∧ False)) ∧ (True ∨ p4)) ∨ (p4 ∧ (p2 → p2)))) ∧ p2) ∨ ((True ∧ False) → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205428418758533455929950745708 : (((p4 ∧ (p5 → p5)) → (p1 ∨ p3)) ∨ (((((p1 ∧ (p3 ∧ ((p5 → p1) → ((p1 → p1) → (p4 → p5))))) ∨ False) ∧ p1) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134662622648093000012327482909 : ((((p5 ∨ (((p2 → p3) ∨ True) ∨ (True → (p5 ∧ p1)))) ∨ (((True ∧ (True → (False ∨ p2))) ∧ False) ∧ p3)) → False) ∨ ((p1 ∧ False) → p5)) := by
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
theorem thm_5_vars_199788666286189231587514315970 : (((((p5 → p2) ∨ p4) ∧ True) ∧ (p3 ∨ p3)) → ((p1 → True) ∧ (((p5 ∨ ((True ∨ p5) ∧ ((p2 → p5) ∨ p1))) → True) → (p2 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116145395570344137509321814270 : (((True ∨ (p3 ∨ False)) ∧ (((True ∧ p4) → p4) → ((True → p1) ∨ (True ∧ ((p4 → p5) → ((p3 ∧ (True ∧ p3)) ∨ p3)))))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344165439577443190469450112302 : (p2 → (p1 ∨ (((p3 ∨ (p5 → (p1 → (((((True ∧ p5) ∧ p4) → p3) ∧ True) ∨ (False ∨ (p4 → False)))))) ∧ (p4 ∨ (p4 ∨ p3))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264308478981131783057825506961 : (True ∧ (((True ∨ False) ∧ (p4 → (p5 → True))) → (False ∨ ((p5 ∨ (False ∨ (p3 → (p2 → (p1 ∧ p2))))) ∨ ((p1 → (p2 ∨ p2)) ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_924180131225056611089642838464 : ((((p4 ∨ ((((p5 ∨ p1) → p4) ∧ (p3 → p3)) ∧ (True ∨ True))) ∧ ((((p1 ∨ (True ∧ (p2 → (p3 ∨ False)))) ∨ True) ∧ p1) ∧ p5)) → p4) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h3.left
      let h22 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
          have h27 : (p5 ∨ p1) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h22
          -- We have shown the premise of h18, we can now drive its conclusion.
          let h28 := h18 h27
          -- One of the premise coincides with the conclusion.
          exact h28
        case inr h29 =>
          -- Conjunctions on the left can always be decomposed.
          let h30 := h29.left
          let h31 := h29.right
          -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
          have h32 : (p5 ∨ p1) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h22
          -- We have shown the premise of h18, we can now drive its conclusion.
          let h33 := h18 h32
          -- One of the premise coincides with the conclusion.
          exact h33
      case inr h34 =>
        -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
        have h35 : (p5 ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h18, we can now drive its conclusion.
        let h36 := h18 h35
        -- One of the premise coincides with the conclusion.
        exact h36
    case inr h37 =>
      -- Conjunctions on the left can always be decomposed.
      let h38 := h3.left
      let h39 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h40 := h38.left
      let h41 := h38.right
      -- Disjunctions on the left can always be decomposed.
      cases h40
      case inl h42 =>
        -- Disjunctions on the left can always be decomposed.
        cases h42
        case inl h43 =>
          -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
          have h44 : (p5 ∨ p1) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h39
          -- We have shown the premise of h18, we can now drive its conclusion.
          let h45 := h18 h44
          -- One of the premise coincides with the conclusion.
          exact h45
        case inr h46 =>
          -- Conjunctions on the left can always be decomposed.
          let h47 := h46.left
          let h48 := h46.right
          -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
          have h49 : (p5 ∨ p1) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h39
          -- We have shown the premise of h18, we can now drive its conclusion.
          let h50 := h18 h49
          -- One of the premise coincides with the conclusion.
          exact h50
      case inr h51 =>
        -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
        have h52 : (p5 ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h39
        -- We have shown the premise of h18, we can now drive its conclusion.
        let h53 := h18 h52
        -- One of the premise coincides with the conclusion.
        exact h53
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301053286754981982739150530798 : (False ∨ ((((True ∧ (p5 ∨ (p5 ∨ True))) ∨ p5) → (True → False)) ∨ (((p5 → p5) → (False ∧ (p4 ∧ ((p1 ∨ (p1 ∧ p2)) ∨ p3)))) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164787438728932694329358395048 : (((((p1 → p3) ∧ (p2 → True)) ∧ ((p2 ∧ (p5 ∧ p1)) ∨ (p3 ∧ (p4 ∧ p4)))) ∨ p3) ∨ (((p4 ∨ (p4 ∧ p4)) ∧ (p2 ∨ p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164998406768898377644483646699 : ((((((p3 → p2) ∨ ((p4 ∨ p4) ∨ p2)) → p2) ∨ ((True → p4) ∧ (p2 ∨ p3))) → p3) ∨ (((False → (p5 → (p4 ∨ p4))) → p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689237458292283750122276686634 : (((((p2 ∧ (False ∨ (p2 ∧ (True → (((p4 ∧ (False ∨ p4)) ∧ p4) → p1))))) → p1) ∨ (p3 ∨ ((False ∧ (p3 ∨ False)) → (False ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738453971548128817915797371550 : ((((p1 ∧ p2) ∨ (p2 ∨ ((p2 ∨ ((p1 → ((p5 ∧ p3) ∧ (p3 ∧ (((p5 ∧ p3) → p2) ∨ p4)))) ∧ p4)) ∨ (False ∧ (p1 → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129031838791870959742421589266 : (((((p1 ∧ (((False ∨ (p2 → (p2 ∧ (p3 ∨ p1)))) ∧ p3) ∧ p1)) ∧ ((False ∨ (p1 ∧ p1)) ∧ p2)) ∧ p1) ∨ True) ∧ (p1 → (p4 → True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317618121987215338398783440526 : (p4 ∨ ((((((True → ((p4 ∧ (True ∨ p3)) → p3)) ∧ (p5 ∨ False)) ∨ ((p3 → ((p4 → p3) ∨ (p1 → p2))) ∧ p5)) ∨ p5) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40799973362866991724059549472 : ((((True ∨ (p2 ∨ ((((p2 ∨ p3) ∨ ((p2 ∧ False) ∨ ((p1 ∨ p2) → (p2 ∨ (p3 ∨ True))))) ∧ (True ∨ p5)) ∧ True))) → p1) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256137900207027319376374333816 : ((True ∨ p5) → (p3 ∨ (p3 ∨ (p5 ∨ ((False → ((((((p2 → (p4 ∨ True)) ∨ True) ∨ p4) ∧ False) ∨ p2) → p2)) ∨ ((False → True) ∧ p2)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- False on the left can always be used.
          apply False.elim h7
        case inr h10 =>
          -- False on the left can always be used.
          apply False.elim h7
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h7
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h3
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600451914842242557263716023372 : ((((True ∧ ((p5 → ((p4 ∧ (p3 ∧ True)) ∨ (((p5 ∧ True) ∨ (p4 ∨ p3)) ∧ p2))) ∧ ((p4 → False) ∧ (False ∧ (p5 → True))))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185521537798318736542166082726 : ((p3 ∨ ((p4 ∨ (p3 ∨ ((p2 ∨ (p4 ∧ p1)) ∨ False))) ∨ True)) ∨ (((p1 ∧ (p5 → True)) → (((False ∧ p5) ∨ (False ∧ p5)) ∨ p4)) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343079254771663499058276819432 : (p2 → (((p3 → p2) ∨ p3) ∧ ((((True ∨ (p5 → (True → ((p4 ∧ p3) ∧ (p5 ∨ False))))) → (False ∧ (p4 ∨ False))) ∨ p4) ∨ (True ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256754885590839710145086235549 : ((p1 ∨ p2) → ((((((p4 ∨ p3) ∨ p5) → (p2 ∨ ((True ∧ False) ∧ p1))) → (p3 → (p3 → p1))) ∨ ((True → p5) → (p2 → p5))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49146869488338711065373884201 : ((((p5 ∨ (p1 ∧ (True → (p3 ∨ ((False ∧ True) → p4))))) → (((p4 ∨ (p3 ∧ p1)) ∧ (p2 → p5)) ∨ p2)) ∨ (True ∨ (p5 ∨ p4))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319699197344739097312110682079 : (p4 ∨ (((p4 ∨ (False → (p4 ∨ p3))) ∨ p3) ∧ ((True ∧ (((((p4 ∨ False) → p5) ∨ (p3 ∨ (p5 ∧ False))) → False) ∨ (p4 → p4))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350088230883210985683357523607 : (p4 → ((((((p2 ∨ p2) ∨ (p1 ∨ False)) ∧ (p4 ∨ (((p3 ∨ p3) → p4) ∧ p1))) ∨ (p5 ∨ (p3 → p2))) ∧ ((p2 ∨ p1) ∨ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206157467480972448505006769164 : ((p5 ∧ ((False ∧ (p5 ∧ p1)) ∨ False)) ∨ (True ∨ (((((p2 ∨ ((p5 → False) → (p4 ∨ p1))) → p3) ∨ (p4 ∨ p1)) → (False ∧ p2)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136167420771158418526634314532 : (((p4 → (p5 ∧ (p2 → ((p5 → p2) → False)))) → (((((p1 ∧ (p2 → p1)) → p4) ∨ p5) ∧ p3) ∨ (True ∨ p1))) ∨ (p3 ∧ (p2 → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324246963886979455575592470450 : (p5 ∨ ((p1 → (p2 ∨ ((False ∧ p1) ∨ (True ∨ True)))) ∧ ((((p1 → p5) ∧ (p1 → p4)) → ((p3 → (p5 → p1)) ∨ p1)) ∨ (True ∨ p3)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117167467525564715600022876145 : ((True ∧ (((((p2 ∧ (((p1 → (p4 ∨ (True ∨ p4))) → p5) ∨ ((False ∧ p5) ∨ p1))) ∨ (p5 ∨ p2)) ∧ False) → p2) → p4)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57728076113218087401136133563 : ((((p1 ∨ p5) → p2) → (((p4 ∨ (p5 ∨ p4)) ∧ False) ∧ (False ∨ (((p5 ∧ (((p1 → False) ∨ p4) → True)) ∧ p1) → (False ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166116305624609586977343533760 : ((True ∧ ((p1 ∨ ((((p2 ∧ p4) ∨ p5) ∧ ((p3 ∧ p5) → (True → p1))) → p2)) ∧ p2)) ∨ ((((p2 ∧ (p1 ∧ p3)) → False) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219084379269941328343299433396 : ((p5 ∧ (p5 → (p1 ∨ True))) → (((p3 ∧ False) ∨ ((p2 ∨ (((((p1 → True) ∧ False) → p4) → p3) ∨ p1)) ∧ p1)) ∨ ((p5 ∧ True) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637538422827812037730809548826 : ((((((p4 → (((p1 ∨ p4) ∨ (p1 ∨ p5)) → p2)) ∨ p3) ∨ (((p5 ∧ True) ∨ True) → ((p5 ∧ (p2 ∧ (p4 → p4))) ∨ p1))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644165427648147257645361543492 : ((((True ∨ (p5 ∨ ((p4 ∧ ((p2 → ((True ∧ (False ∧ (((True → (p2 → p5)) ∨ p2) → (p1 → p4)))) ∧ p4)) ∨ p5)) → False))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50606286225877824790838977312 : ((((p5 ∨ ((p1 → (p5 → (True → p5))) ∧ ((((p1 → True) ∧ p5) ∧ p3) ∧ True))) ∨ (False → p1)) → (False ∧ (p2 ∧ (p3 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223831079536792115476462279857 : ((p3 ∨ (True ∨ p1)) ∧ ((p4 ∧ ((p3 ∨ (((p4 ∧ p2) ∨ (False → p3)) ∨ (((p1 ∨ False) ∨ p1) → True))) ∨ p5)) ∨ (False → (p3 ∨ True)))) := by
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
theorem thm_5_vars_336306472829963997614122984694 : (p1 → (((p4 ∧ (p2 ∧ ((True → True) ∨ p3))) → ((((p5 → (True ∨ (p3 → (((p4 ∨ True) ∨ p5) → False)))) → False) ∨ p2) ∨ p1)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157238480875734605103781410543 : ((((True ∧ (False → (p5 ∨ (p2 → (p4 ∧ False))))) ∧ ((((p3 ∧ p5) → p5) → True) ∨ p1)) → p1) ∨ ((p2 → p2) → (p3 ∨ (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116067093285256750253184506491 : ((((p2 ∨ False) ∧ p1) ∧ (((((((((p3 ∨ (True ∧ p3)) ∨ False) ∨ False) ∨ p4) ∨ True) → p1) → True) ∧ (p1 ∨ p5)) ∨ False)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_577297979699489297471011020882 : (((p3 → (((((False → False) ∧ (((p2 ∨ True) → False) ∧ p5)) ∧ p5) ∧ ((p2 → (p3 ∨ (p4 ∧ True))) → (False ∨ p5))) ∨ (False ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39230360681606326284932133541 : (((True ∧ (p5 ∨ (((((((p5 ∧ p4) ∧ (p1 ∧ (True ∨ p2))) ∨ True) → p4) → p5) ∧ (p5 → (p3 ∨ (p4 ∧ p2)))) → False))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179130599588829976077721572171 : ((p1 ∧ (((p3 → p2) ∨ (False ∧ False)) ∧ (p5 ∧ (True → (p4 ∨ p5))))) ∨ (True ∨ (p5 ∧ (p5 ∧ ((p4 → p2) ∧ ((p2 → p4) ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184781357843027371877560024697 : ((((p4 ∨ (p4 ∧ False)) ∨ p3) ∨ (p4 ∨ ((True ∧ p2) ∧ p5))) ∨ ((p1 → (p2 → p1)) ∧ ((True ∨ (p5 ∧ (p3 ∨ (p4 → False)))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32611573029512362681185085724 : ((p2 ∨ ((p4 → (False ∧ ((p5 ∧ p2) → False))) → (((((p4 ∨ (((p3 ∨ p1) ∨ True) → False)) ∨ (True → p3)) → p2) ∧ p3) → p2))) ∧ True) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((p4 ∨ (((p3 ∨ p1) ∨ True) → False)) ∨ (True → p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41112219700739436519494490497 : ((((p1 ∧ ((p2 ∨ (p2 ∨ ((((p4 ∨ False) ∨ (p5 ∨ True)) → True) → (p4 ∨ (p2 → False))))) → p2)) ∧ ((p1 ∨ p5) ∧ p4)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_73539445499046180694708598844 : ((((((True ∨ p1) → (p4 ∧ ((((False ∨ (True ∧ ((False ∨ p5) → True))) → p2) ∧ p4) ∧ False))) → p5) → (p3 ∧ (True ∨ p4))) ∨ p3) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (((True ∨ p1) → (p4 ∧ ((((False ∨ (True ∧ ((False ∨ p5) → True))) → p2) ∧ p4) ∧ False))) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h5 : (True ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h6 := h4 h5
      -- We need to get the right conjuct of h6 based on <expert-advice>.
      let h7 := h6.right
      -- We need to get the right conjuct of h7 based on <expert-advice>.
      let h8 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h3
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114633159249629213930358494540 : ((((p4 → ((p2 ∨ ((p3 → (p4 → (p4 ∨ True))) ∧ (False ∧ False))) ∨ False)) ∨ p1) ∨ (((p4 ∧ (False ∨ p3)) → p4) → True)) ∨ (p2 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314656312218006534192103990205 : (p3 ∨ ((((True → False) ∨ False) ∧ (((p1 → ((True ∧ (p5 → p4)) ∧ False)) ∨ p2) ∨ p3)) ∨ (False → (False ∧ ((p1 ∨ True) ∨ (p3 ∧ True)))))) := by
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
theorem thm_5_vars_308395203630329176501094788673 : (p2 ∨ (((True ∧ ((((p4 ∧ False) ∧ True) ∨ p1) ∧ (p2 ∧ (False → ((((p5 ∨ False) ∧ p2) ∨ (p2 ∧ (False ∧ True))) ∧ p5))))) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55518909384128982002225651683 : ((((p3 ∨ p3) ∨ ((p4 ∧ p5) → True)) → (((p5 ∨ (True → (((p3 ∧ p4) → p5) → (p2 ∧ False)))) ∧ p1) ∨ ((p5 → p5) ∨ p2))) ∨ p3) := by
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694266768873479519555284196337 : ((((((p1 ∧ p4) ∧ p2) ∧ ((((False ∧ (p5 ∧ True)) → p4) → p2) ∨ p3)) ∨ ((((p1 ∨ p1) ∧ (p1 → p2)) ∧ (p5 ∨ p1)) → True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657703470978254875845735282666 : (((((p2 → p3) → (((p2 → (False → ((((p2 → ((True ∧ p2) ∧ p1)) ∨ True) ∨ True) ∧ p3))) → p5) → (p3 → False))) ∨ (True → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42667269498586116812302787773 : (((p4 ∨ (((p3 ∨ p5) ∧ True) ∨ (p4 ∨ (p3 → ((p4 ∨ (((True ∨ p2) ∧ p1) ∧ False)) ∧ ((True ∧ p5) → (p4 ∨ True))))))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224894597587688315947844753198 : ((p5 → (True ∨ p2)) ∧ ((((p3 → ((p5 ∨ p3) ∨ True)) ∧ ((p2 ∨ p1) ∧ (False ∨ False))) ∨ ((False → True) ∧ (p5 ∨ p3))) ∨ (p5 ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



