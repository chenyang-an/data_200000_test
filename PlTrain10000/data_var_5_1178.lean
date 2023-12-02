variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40179350840474115401708972925 : (((((p5 ∨ ((p4 ∧ p3) → p3)) ∧ (((True → (((False ∨ p5) ∧ (p3 ∧ (p3 ∨ p5))) → (p4 → p3))) ∨ True) → p2)) ∧ False) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149034816255515921510719987739 : (((p2 ∧ (p1 → True)) ∨ ((((p2 ∨ p3) ∧ p5) → False) ∧ (((p1 ∧ False) ∨ (p1 ∧ p3)) ∨ (False ∧ p3)))) ∨ ((p1 ∨ p2) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42626386548417044257060588484 : (((p3 ∨ ((p4 → ((p5 ∧ False) → p1)) ∧ (p3 ∧ (((p3 ∨ False) ∨ ((p4 ∧ (p3 ∧ (p2 → (True → p2)))) ∨ True)) ∨ True)))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184246262260691699380622512727 : (((((p1 → p5) ∨ (((p3 → p5) → p5) ∨ p4)) → p5) → p1) ∨ ((p5 ∧ (p5 → (p2 → False))) → ((((False ∧ p2) → p4) → p3) ∨ True))) := by
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
theorem thm_5_vars_185286327544318439068676013879 : ((p2 ∧ (((((True → False) ∨ p1) → False) ∨ p4) ∨ (p2 ∧ False))) ∨ (True ∧ (False → (p2 → (((p5 ∧ (p4 ∧ (p5 → False))) → p2) ∨ p1))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165005829590635713763337524000 : (((((True ∧ p3) → ((p2 ∨ p5) ∨ p1)) ∧ (p5 ∨ ((p4 ∨ (p1 ∨ False)) → False))) → p4) ∨ (True ∨ (p4 → (True → (p5 → (False → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209409374243132497633435275399 : ((p2 → (((p5 ∧ p4) ∧ False) ∧ False)) → ((((((p4 ∧ False) ∨ p5) ∨ True) ∨ p2) ∧ True) ∨ ((True ∧ (((True → p1) → p3) ∧ p5)) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209577993390975841326237318298 : ((p5 → (True ∧ (True → (False → p4)))) → ((((p2 ∧ ((p3 → p4) → (False → p5))) → (p3 ∧ (p5 ∧ (p2 ∨ p1)))) ∧ p2) → (p5 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p2 ∧ ((p3 → p4) → (False → p5))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h5
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307394392711238206406995663514 : (p1 ∨ (p4 ∨ ((True ∨ (p3 → p1)) → (((((False ∧ (p5 ∨ p2)) ∨ ((True ∨ p5) ∨ p1)) ∨ False) ∨ (p2 ∨ True)) ∨ ((p4 → p3) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147415050365469785786928682572 : (((((p1 → (p3 → p2)) ∧ p4) → (p1 ∨ (False ∨ ((p2 ∧ ((True → p5) ∨ p5)) ∨ (p3 ∨ True))))) ∨ False) ∨ (p2 ∧ ((False ∧ False) ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
theorem thm_5_vars_790661513275848096421012393913 : (((p5 ∨ (p4 ∨ (p5 ∧ (((p2 → p1) ∨ False) ∧ (((p2 → (((p5 ∧ False) ∨ ((p5 → p2) → True)) ∧ p2)) ∨ (p1 ∨ p2)) ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44042235045354469248259145512 : ((((False ∨ ((((p3 ∨ p4) → False) ∧ (False ∨ (False ∨ (((p4 → p5) ∨ p4) ∧ ((True ∨ p2) → p4))))) → p3)) → (p5 → p5)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740758592831862157485226533715 : ((((p2 ∨ p5) ∨ (((((((True ∨ True) ∧ (p1 → p5)) ∧ (p5 → p4)) → p5) ∧ p1) → (p5 ∨ True)) ∧ (p3 → ((p2 ∧ False) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112266486175835351828157892142 : (((p5 ∨ (((((p5 ∧ p3) ∧ p2) ∨ (True ∧ p2)) ∧ p3) ∨ (p2 → (p4 ∨ (p4 ∨ ((p4 → p2) ∨ (p4 → p5))))))) ∨ p1) ∨ (p3 ∧ p2)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300408806870566320290109953379 : (False ∨ ((p2 ∨ (p1 ∨ (p2 ∧ ((((((p1 → True) ∨ True) → p5) ∧ p4) ∨ ((p4 ∨ p4) ∧ (p1 ∨ p5))) ∧ p5)))) ∨ (True ∨ (False ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232346886096846012910930860057 : (((p4 → p1) → p4) → ((((p1 ∨ (p5 → p2)) ∧ ((True → p2) → (((p1 ∨ p1) ∨ p1) ∨ p3))) ∨ (p3 ∨ True)) ∨ ((p4 ∧ p2) ∧ p2))) := by
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
theorem thm_5_vars_54937846249961237472662266850 : ((((p4 → ((p5 ∧ p1) ∨ p4)) → p2) ∧ ((p4 ∧ ((p5 ∨ p1) ∧ (False ∨ ((p5 ∨ p5) ∧ (p5 ∧ (p1 ∧ (p3 → True))))))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62851877124048520228838406681 : ((p4 ∧ ((p5 → (p2 ∨ (True ∨ p3))) ∧ ((p5 ∧ p3) ∧ (((((p5 ∨ p3) ∨ p2) ∨ True) ∧ False) ∧ (((p1 → True) ∨ p2) → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340883267539072851615748985346 : (p2 → ((((((p3 ∧ True) ∨ ((False ∧ (p5 → (p1 → p1))) ∨ p2)) → True) → p5) ∧ ((p2 ∧ (p4 ∧ p3)) ∧ (p5 → (False ∧ False)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47088581039669077175586142315 : (((((p2 → (p2 → False)) → (((p3 ∧ ((p2 ∧ (False → (p2 ∧ (True ∨ p2)))) → False)) ∨ p5) ∧ p5)) → (p5 ∧ p5)) ∨ (True ∨ p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117603847302091249139324507343 : ((p2 ∧ (p5 ∨ ((p1 → (((p2 → (False → (p3 ∧ p2))) → p3) ∨ p3)) → ((p3 ∨ False) → ((False ∨ (p1 ∧ p5)) ∨ p2))))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114641867770222087267857994067 : (((((p4 → (True → (p3 → p4))) ∧ (((p4 ∨ p1) ∨ True) ∧ p4)) ∧ (p4 ∨ p2)) ∨ ((p2 ∨ (False ∧ (False ∧ False))) ∨ p4)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2659371009298031494253908446 : ((((p3 ∨ True) → p5) → (p4 ∨ p2)) ∨ (p4 ∨ ((((p3 ∨ True) ∨ (p4 ∨ True)) ∧ ((True → True) → (True → True))) ∧ (True ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655529539265890260056755778633 : ((((((p5 ∨ (p2 → (((p2 → (p3 → False)) → (p1 ∨ p3)) ∧ (p5 → ((True → p4) → p4))))) → p3) → (False ∧ False)) ∨ (p1 ∨ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_323660433075886858355444497030 : (p5 ∨ (((p5 ∨ (p2 ∧ ((((False → p2) → ((False ∧ p1) ∨ (p2 ∧ p4))) ∧ p1) → True))) ∧ (p1 ∧ True)) ∨ (p3 → ((p5 ∧ p5) ∨ True)))) := by
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
theorem thm_5_vars_152055828560964930280009186915 : ((((p5 ∧ (p2 → (False ∨ (p3 ∧ (p2 → p2))))) → p3) ∨ (p2 ∧ (((True ∨ True) ∨ (False → p2)) ∨ p2))) → (p3 → (p1 ∨ (False → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
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
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- False on the left can always be used.
          apply False.elim h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776403606627877902065587206466 : (((p1 ∨ (((p4 ∨ (p5 ∧ ((((p2 ∧ False) ∨ p4) ∧ ((p3 → (p2 ∨ p5)) ∧ (p4 ∨ ((False → False) ∨ p4)))) → False))) ∧ p1) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45165081896071566090851245764 : (((True ∧ ((p1 ∧ (((p4 ∨ (p4 ∨ (p2 → p2))) → (p4 ∧ False)) ∨ False)) ∧ (((p5 → (p3 ∧ (p4 → p1))) ∨ True) ∨ True))) → False) ∨ False) := by
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
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h11 : (p4 ∨ (p4 ∨ (p2 → p2))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h13 := h8 h11
        -- We need to get the right conjuct of h13 based on <expert-advice>.
        let h14 := h13.right
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h16 : (p4 ∨ (p4 ∨ (p2 → p2))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h17
          -- One of the premise coincides with the conclusion.
          exact h17
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h18 := h8 h16
        -- We need to get the right conjuct of h18 based on <expert-advice>.
        let h19 := h18.right
        -- False on the left can always be used.
        apply False.elim h19
    case inr h20 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h21 : (p4 ∨ (p4 ∨ (p2 → p2))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h22
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h23 := h8 h21
      -- We need to get the right conjuct of h23 based on <expert-advice>.
      let h24 := h23.right
      -- False on the left can always be used.
      apply False.elim h24
  case inr h25 =>
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157244174638937009863562733123 : (((((p3 → (p3 → p5)) → (p3 ∨ (p4 ∧ p5))) → (p1 → (((p1 ∨ p4) ∨ p4) ∧ False))) → p2) ∨ ((p3 → ((p5 → p2) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166585971004544879986829349797 : ((True → ((((p2 ∧ p2) ∨ p4) ∨ p4) → (p3 → ((p5 ∧ p5) ∨ ((p4 ∨ p4) ∨ p1))))) ∨ ((True ∨ (p2 ∧ p2)) ∨ (p4 ∧ (p1 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40759215086923476735811548028 : (((((True ∨ p3) ∨ ((p3 → (((p1 ∧ (p1 ∨ (p5 ∧ (p1 ∧ (p2 ∨ p4))))) ∨ p1) ∧ ((True → p2) ∨ p4))) ∧ p4)) → p1) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117317809701396335486853458801 : ((False ∧ (((p5 → p4) → (True → ((p1 → (True ∨ True)) → (p3 ∨ p5)))) ∨ (p3 ∨ ((p2 ∧ (p2 → p2)) ∨ (p3 → p4))))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354754293858165923190642397573 : (p5 → (((False ∨ ((p3 ∨ (p4 ∨ ((p4 ∧ (p4 → p1)) ∨ False))) ∧ (p3 ∧ False))) ∧ ((p1 ∧ p4) → (p5 ∧ (p5 → (p5 → False))))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137083693033208843677604808355 : ((True ∧ (((p3 → ((p2 ∨ (p3 → p3)) ∨ (p5 → (False → (p5 → p3))))) → ((p4 → True) ∧ (p1 ∨ p4))) ∧ True)) ∨ ((False ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262157459970667530498300429253 : (True ∧ ((((p5 ∧ (((p5 → p3) ∨ p1) ∨ False)) ∧ ((((p1 → p1) → p2) ∧ (((p3 → p2) → p4) ∧ (p4 ∨ p5))) ∧ p5)) ∨ p2) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158001909709817987976499781941 : (((p2 ∨ (p5 → (((p5 → p1) → p5) ∧ p1))) → (p2 ∧ ((True ∨ (p2 ∨ (True → p5))) ∧ p2))) ∨ ((True ∧ (p2 ∨ (False → True))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358358215679155289572039757957 : (p5 → (True → ((p4 → ((False ∨ ((True → (((p2 ∨ p3) ∧ p4) ∧ p4)) ∧ (True ∨ p5))) → False)) → ((p1 → p3) → ((p2 → p4) ∨ p5))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682334064565752185562067385419 : (((((((False → p3) ∨ True) ∧ (False → (((p5 ∨ False) → (p5 ∧ p1)) ∧ p5))) ∨ (p1 → p3)) ∧ ((p1 ∧ p3) → (p4 ∨ (True → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317883103873417509425650754312 : (p4 ∨ ((True ∧ ((p2 ∧ (p2 → (((p5 ∨ (p5 ∨ p4)) ∧ True) ∧ p3))) ∧ (((((p4 → p3) → False) ∨ p2) ∧ (True ∨ p2)) → p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732415061870724169756678238 : (((p5 ∨ (p5 ∨ (p5 → p5))) ∧ ((((True ∧ (p5 → (p4 ∧ p2))) → p5) ∨ (((True ∧ p3) → (p3 → True)) ∨ p2)) ∧ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301379868773552191339081736901 : (False ∨ (((p1 ∧ p4) ∨ (True → False)) ∨ ((p5 ∨ False) → (((p4 ∨ p1) ∧ (True ∧ (p4 ∧ (p4 ∧ True)))) ∨ (True → (p1 → (p1 ∨ p4))))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192816943098516862636189077648 : (((p2 → ((False ∧ False) ∧ ((p1 ∧ p1) → False))) → p4) → ((p1 ∧ p3) ∨ ((p4 ∨ (True ∨ (p3 ∨ p5))) ∨ (p1 → (p4 ∧ (p2 ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_790350519121013901880029301920 : (((p5 ∨ (p3 ∧ (True → (((p3 → (True → (((p2 → ((p2 ∧ False) ∧ False)) ∨ p2) ∨ (((p4 ∨ True) ∨ False) ∧ p2)))) → p1) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53654467786928173837371888601 : ((((p4 → (True ∨ p2)) → ((p2 ∨ True) ∧ (p2 ∨ p4))) ∧ (((p2 ∧ (p1 → (((p2 → p1) ∧ p2) ∧ p5))) ∨ True) ∨ (True → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171406626802440981811769272133 : ((((p5 ∧ ((p4 ∧ True) → True)) → ((p1 → ((p5 ∨ p4) ∨ True)) → False)) ∧ False) ∨ (False → ((True ∧ (((True → p3) ∧ p1) → False)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41204539699443373649676438128 : ((((p2 ∨ (p4 ∨ ((False ∧ p4) → (p2 → (p3 ∧ (True ∧ (((p1 ∨ p1) → True) ∧ (p2 → p5)))))))) → ((False → False) → False)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50211701142305839675310548336 : (((((((p5 → p4) ∨ (p3 ∨ (p3 ∧ (p2 ∧ p2)))) ∧ (p1 ∨ p4)) ∧ (p4 → (p4 ∨ p2))) ∨ p3) ∨ (p5 ∨ (p2 → (p2 ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192351876177681660579219398332 : (((True → ((False ∧ p2) ∨ ((p5 ∧ p4) ∧ p1))) ∧ p4) → ((((p3 → p4) ∨ p3) ∧ (p3 ∨ True)) → ((p4 → (p3 ∧ p5)) ∨ (p5 ∧ True)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h1.left
      let h8 := h1.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h10 := h7 h9
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- False on the left can always be used.
        apply False.elim h12
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h15.left
        let h18 := h15.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h17
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h1.left
      let h21 := h1.right
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h22 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h23 := h20 h22
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- False on the left can always be used.
        apply False.elim h25
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- Conjunctions on the left can always be decomposed.
        let h30 := h28.left
        let h31 := h28.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h30
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h32 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h1.left
      let h35 := h1.right
      -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
      have h36 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h34, we can now drive its conclusion.
      let h37 := h34 h36
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h38 =>
        -- Conjunctions on the left can always be decomposed.
        let h39 := h38.left
        let h40 := h38.right
        -- False on the left can always be used.
        apply False.elim h39
      case inr h41 =>
        -- Conjunctions on the left can always be decomposed.
        let h42 := h41.left
        let h43 := h41.right
        -- Conjunctions on the left can always be decomposed.
        let h44 := h42.left
        let h45 := h42.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h44
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h46 =>
      -- Conjunctions on the left can always be decomposed.
      let h47 := h1.left
      let h48 := h1.right
      -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
      have h49 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h47, we can now drive its conclusion.
      let h50 := h47 h49
      -- Disjunctions on the left can always be decomposed.
      cases h50
      case inl h51 =>
        -- Conjunctions on the left can always be decomposed.
        let h52 := h51.left
        let h53 := h51.right
        -- False on the left can always be used.
        apply False.elim h52
      case inr h54 =>
        -- Conjunctions on the left can always be decomposed.
        let h55 := h54.left
        let h56 := h54.right
        -- Conjunctions on the left can always be decomposed.
        let h57 := h55.left
        let h58 := h55.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h57
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233370114174426077395910553779 : ((False ∨ (p1 ∧ p4)) → (((p2 ∧ p3) ∨ (((((p2 ∨ p3) ∨ ((p5 ∨ False) ∧ False)) ∨ p2) ∨ ((p1 ∧ p5) → (p1 ∨ False))) ∨ p1)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769456410174448389048688503331 : (((p5 ∧ (p2 ∧ ((((p2 ∨ ((p4 ∨ ((p1 ∧ (p1 ∨ p1)) ∨ (True ∨ True))) → ((p2 ∧ p2) ∨ p4))) ∨ p4) → p3) ∧ (True ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642775523324984934963186545675 : ((((p1 ∧ (p1 ∨ (False → (p1 ∨ ((True → ((p1 → ((True ∨ (p4 → p2)) → ((p1 → p2) ∨ (p3 ∨ p2)))) → p3)) → True))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721132972673347861890704513415 : (((((False → True) ∨ (p2 → p5)) → (p4 ∨ ((False ∨ (p3 ∨ (p2 ∧ ((True ∧ (True → ((p1 → (p1 ∧ False)) ∧ p1))) → p1)))) ∨ True))) ∨ p3) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_457254510971158716328213465037 : ((((((((p1 ∧ ((True → (False → p5)) ∧ (p3 ∨ False))) ∧ True) ∨ p3) ∧ (p3 ∨ p3)) ∨ p2) ∨ ((p5 ∧ p2) → ((True → p1) ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57930322098294681088888248582 : (((True → (p5 ∨ p5)) → ((p2 ∧ ((False → p2) ∧ (((p4 → (False ∨ False)) ∧ False) ∧ (p3 ∧ ((p1 → (p5 ∨ p2)) ∧ p1))))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242975170869946743426923987399 : ((p4 → True) ∧ (((((p3 ∧ (p1 ∨ p5)) ∨ (p2 ∨ ((p1 ∧ p1) ∧ p1))) ∨ p4) ∨ ((p2 ∨ (p4 ∨ (p2 → p3))) ∨ (False → True))) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232901269656666548484846452289 : ((p3 ∧ (p2 ∧ p1)) → ((p1 ∧ (p2 ∧ (p3 ∨ (True ∨ ((p4 ∧ p5) → False))))) → (p2 → (((True → p1) → (True → (p4 ∧ p2))) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h1.left
      let h16 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h1.left
      let h21 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142881942717640793019032202718 : ((p4 ∨ (True ∧ ((p3 → ((p2 ∨ False) ∨ p2)) ∨ (True ∨ (p5 ∧ (p1 ∨ ((True ∨ (p5 ∨ (False ∧ p1))) ∧ p5))))))) → (False ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- False on the left can always be used.
        apply False.elim h11
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
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h21
            -- False on the left can always be used.
            apply False.elim h21
          case inr h22 =>
            -- Disjunctions on the left can always be decomposed.
            cases h22
            case inl h23 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h24
              -- False on the left can always be used.
              apply False.elim h24
            case inr h25 =>
              -- Conjunctions on the left can always be decomposed.
              let h26 := h25.left
              let h27 := h25.right
              -- False on the left can always be used.
              apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337662656169160204067088386639 : (p1 → (((p3 ∧ (True ∧ ((p5 ∨ p2) ∨ (p3 → (True ∨ False))))) ∨ (p2 → ((p1 → p5) ∧ p3))) ∨ (p1 ∨ (((p2 ∨ p3) ∨ p5) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115757870592573069662638504801 : (((p5 ∧ (p1 ∨ ((p2 ∧ False) ∨ p1))) → (False ∧ (((False ∧ (p4 ∧ (p5 → p5))) ∨ p4) ∨ (p5 → (p5 ∧ (False → p2)))))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54544434811488933603479618872 : (((True ∧ ((True → False) ∧ (p1 → (True → p3)))) ∨ (p1 → (p3 → ((((p2 ∨ False) ∨ (p1 ∧ True)) ∨ p4) → ((False → p2) → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727188729033294899818865424195 : ((((False ∧ (False ∧ p5)) ∨ (((p1 ∨ p5) ∨ p1) ∨ ((((p3 ∨ False) ∨ p1) → ((p1 → ((p5 ∧ p4) ∧ (p2 ∧ p5))) ∧ p1)) ∨ True))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_743430277514545242807937493476 : ((((p5 → p3) ∨ ((((p5 ∨ ((p4 ∨ (p3 ∧ (False ∨ ((False → True) ∧ (p1 ∨ p3))))) ∨ (False ∧ False))) → p5) ∨ p5) ∧ (False ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_23780237528925410669762700963 : ((((p1 ∨ p1) → (p4 ∨ False)) ∨ (((p5 ∨ True) → (p4 ∨ (True → ((p5 ∧ p2) → p2)))) ∨ ((p1 → True) → ((p1 → False) ∧ True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687563498502871400497218764514 : (((((((p4 ∨ ((((p1 ∧ False) ∨ p3) ∧ p2) ∧ (True → True))) ∨ p4) → False) → p1) ∧ (((p1 → (p2 ∨ p4)) ∧ True) ∧ (p2 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216726269886973725709932308928 : ((((False ∨ p5) → False) ∧ True) → ((p2 → ((p4 ∨ p3) → (p1 → False))) → ((p5 ∨ (p5 ∨ p5)) → (((True ∨ p4) ∧ p1) ∧ (p3 ∨ True))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h1.left
      let h10 := h1.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h1.left
      let h13 := h1.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h1.left
    let h16 := h1.right
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h17 : (False ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h18 := h15 h17
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h1.left
      let h22 := h1.right
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h23 : (False ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h20
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h24 := h21 h23
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h1.left
      let h27 := h1.right
      -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
      have h28 : (False ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h25
      -- We have shown the premise of h26, we can now drive its conclusion.
      let h29 := h26 h28
      -- False on the left can always be used.
      apply False.elim h29
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h30 =>
    -- Conjunctions on the left can always be decomposed.
    let h31 := h1.left
    let h32 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h1.left
      let h36 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h37 =>
      -- Conjunctions on the left can always be decomposed.
      let h38 := h1.left
      let h39 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314663854424561291304311822335 : (p3 ∨ ((p5 ∧ (p4 ∧ (((p3 → (p1 ∨ (True ∨ (True → (p3 ∨ p2))))) ∧ p4) → p2))) ∨ (((False ∧ True) → True) ∨ ((True ∨ p2) ∨ p1)))) := by
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
theorem thm_5_vars_263924640405231786231822126077 : (True ∧ (((False ∨ ((False ∨ p1) ∨ True)) ∧ ((p5 ∧ ((p3 → True) ∧ True)) → p3)) → (((((True → False) → p1) ∨ (True ∨ p1)) → p5) → p3))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h10 : (((True → False) → p1) ∨ (True ∨ p1)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h11 := h2 h10
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h12 : (p5 ∧ ((p3 → True) ∧ True)) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h11
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h13
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h14 := h4 h12
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h15 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h16 : (((True → False) → p1) ∨ (True ∨ p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h16
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h18 : (p5 ∧ ((p3 → True) ∧ True)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h17
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h19
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h20 := h4 h18
      -- One of the premise coincides with the conclusion.
      exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616759332451978345277327763923 : (((((((p5 ∨ p3) ∨ p3) → ((p2 ∧ p3) ∧ (p3 ∧ p3))) ∨ ((((p5 ∧ (p1 → False)) ∨ p1) → (True → p5)) ∨ (True ∧ p4))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_682745963818011047531540284454 : (((((p2 ∨ ((p3 → False) ∧ p2)) ∨ (p5 ∧ ((p3 ∨ p2) ∨ (p1 ∧ ((p4 ∧ p1) ∧ False))))) ∧ ((False ∧ (p1 → True)) → (p5 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164572920378208963352771171455 : (((((True ∨ p3) ∧ False) ∨ (((((p2 ∨ False) ∨ False) ∧ p3) ∨ (False → p1)) ∨ p3)) ∧ p2) ∨ ((False → (p1 → ((False ∧ p2) ∧ False))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193563652714317971149699645850 : (((False ∨ p2) → (p3 ∨ (((p4 ∧ p1) → p5) ∧ p2))) → ((((p4 → ((p4 ∨ p2) ∧ p5)) ∧ ((p1 → p5) ∧ p2)) → (p1 ∨ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206070494864347131003413211870 : ((p3 ∧ ((p1 ∧ (p4 → False)) → p3)) ∨ ((True → (False → (False → (((p4 ∨ p2) ∧ p3) → p4)))) → (p5 ∨ ((False ∧ p1) ∨ (False → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_193301315311499756450750366328 : (((True ∧ (p3 → True)) ∨ ((False ∧ True) → (p3 ∨ p3))) → ((p4 → ((True → p1) → p2)) → (p3 ∨ ((p4 ∨ p3) ∨ (False → (False ∨ True)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208577284598715331269961162725 : (((True → p5) → (False → (True ∧ p3))) → ((((p4 ∨ (p2 ∨ p2)) ∨ (p4 ∨ (p2 → ((p4 ∨ p4) → p4)))) ∨ (p5 ∨ p5)) ∧ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352162120575700929987052233294 : (p4 → ((p2 → ((False ∧ (p2 → p2)) → p1)) → (((((p1 ∧ (p1 → False)) → p4) ∨ p3) ∨ p4) ∧ ((((False → p4) → False) ∨ p2) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172172180565643722870247417098 : ((((True ∨ (False → p3)) → (p4 → (p4 ∧ (p3 ∧ p5)))) ∨ ((p1 ∨ p2) ∨ True)) ∨ ((p4 → (((p3 ∧ p1) ∨ p4) ∨ (False ∨ p3))) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254758853533564398499153814285 : ((p3 ∧ p4) → ((p1 ∨ (False ∨ (((False ∧ (((p2 ∧ False) ∨ (p3 ∧ False)) ∨ p1)) ∧ p4) ∧ (True ∧ (((True ∨ p1) → p4) ∨ False))))) ∨ p3)) := by
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
theorem thm_5_vars_305197629305948098256166179138 : (p1 ∨ ((p1 → ((((True ∨ False) ∨ p4) ∧ p4) ∨ ((p3 ∧ (p2 ∨ (p5 ∧ p1))) ∧ ((True ∨ p2) → p2)))) ∨ (p3 ∨ (True ∨ (p4 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353348681717435379995753767318 : (p4 → (False ∨ ((p5 → ((True ∧ (p3 ∨ p2)) ∨ (p2 → (p3 → (p4 ∧ (((p3 → False) ∧ False) ∨ (p1 → ((True → p1) → p5)))))))) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678543049231090792589605409407 : (((((p1 ∨ (p2 ∨ False)) ∨ (p5 ∧ ((((False → ((p1 ∧ False) ∨ p1)) ∧ p3) → (False ∧ True)) ∧ p4))) ∨ (((p4 ∨ True) ∨ p3) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300132469834056556901896174382 : (False ∨ (((True ∨ p4) → (((p5 ∨ False) ∧ (((p5 ∨ ((p4 → False) ∨ (True ∨ False))) ∧ ((p5 ∧ p1) ∧ True)) → True)) ∨ True)) ∨ (True ∧ p3))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54852015247415101291655864295 : (((((p2 ∧ (p4 ∧ p4)) ∨ True) ∧ False) ∧ ((True ∧ (p5 ∧ (True ∧ False))) ∧ ((((p4 ∨ True) ∨ True) → (p5 → False)) ∧ (False ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134542208469140934638874569074 : (((((p5 → (((p2 ∧ p5) ∨ (((False ∧ p5) → p4) → p3)) ∨ p5)) ∨ (p1 ∧ ((False ∧ True) ∧ p2))) → p4) → p3) ∨ ((p5 ∧ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116987296815628270406314971794 : (((p5 ∧ p4) → (True → ((((p5 ∨ (p5 ∧ False)) ∨ p4) ∧ (((p4 ∧ True) → False) ∧ (((False ∨ p1) ∨ True) ∧ p4))) ∨ False))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314948629142929819541787188491 : (p3 ∨ ((((p4 ∧ (p2 ∧ p5)) → (True ∧ (p3 ∨ p5))) → False) → ((((True → (False ∧ p1)) ∨ p5) → p4) ∧ (p1 → ((p1 ∧ p4) → p4))))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : ((p4 ∧ (p2 ∧ p5)) → (True ∧ (p3 ∨ p5))) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h14 := h1 h8
    -- False on the left can always be used.
    apply False.elim h14
  -- Implications on the right can always be decomposed.
  intro h15
  -- Implications on the right can always be decomposed.
  intro h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h16.left
  let h18 := h16.right
  -- One of the premise coincides with the conclusion.
  exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208327945023579090455689534892 : (((p1 → p5) ∧ (True ∨ (True ∨ p5))) → (p3 → ((p5 ∧ (((p4 → (p1 ∨ (False ∨ True))) → p2) ∧ ((True ∧ p2) ∧ p3))) ∨ (p1 → True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183894508324915058081080314235 : ((((p1 → False) ∧ ((True → (p2 ∨ (p2 → p4))) ∨ p2)) ∧ False) ∨ (((((True ∧ False) ∧ (p1 ∧ p4)) ∨ (False ∨ (False → True))) ∨ p2) ∨ p2)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241542230704170148797973522716 : ((False → p3) ∧ (((True → p1) → (((False ∨ p1) ∨ False) → p2)) → ((((p5 → False) ∨ ((p4 → p1) ∧ p5)) ∨ (p5 ∨ (False → p4))) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341762768478981259813502584357 : (p2 → ((p5 ∨ ((p2 → (((p3 ∨ False) → p2) → (((p5 ∨ (((p4 ∧ False) ∨ p5) ∧ True)) ∧ (False ∨ p5)) ∧ p2))) → False)) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47105922679595231968198620979 : ((((p1 ∧ ((p1 ∧ (p5 ∧ ((False ∨ p5) → p4))) ∨ ((p3 ∨ ((p4 → p3) ∨ True)) → True))) ∧ ((p2 ∨ p5) ∧ True)) ∨ (False → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610639201031821141105436330988 : ((((((((((p1 ∧ (p3 → p5)) → False) ∧ p2) ∨ p4) ∧ (p4 → (False ∨ (p5 ∧ ((p1 ∨ p5) ∨ p2))))) → (True ∨ True)) → False) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_165805357666431640122094812848 : ((((p3 → False) ∨ False) ∧ (p3 ∨ (p5 → (p3 ∨ (((p2 ∨ (p1 ∧ p5)) → p3) → False))))) ∨ (((p2 ∨ p3) ∧ p5) ∨ (p3 ∨ (False → p3)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60984662931155092637321112243 : ((False ∧ ((((((((p4 → False) ∧ p2) ∧ False) ∧ (((p3 ∧ p5) ∨ p5) ∧ p2)) ∨ ((p1 ∨ (True ∨ False)) ∨ p4)) → p2) ∧ True) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620689055121160361932585480421 : (((((p1 ∧ p3) → (p5 → (p2 ∧ ((((p2 → False) ∨ p2) → (p3 ∧ (p2 → p4))) ∨ (p4 ∨ ((False ∨ p2) ∧ (True → p5))))))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199092996494864915344546685207 : ((((p5 → (True → (p4 ∧ True))) → p1) ∧ p1) → (True ∧ ((p1 → ((p2 ∧ ((p4 → False) → (True → (p2 → (p5 ∧ p1))))) ∨ p1)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42438020303860730241849036153 : (((p5 ∧ (p4 ∧ (((((p2 → p4) ∧ True) → (p5 → (p1 → (((p5 ∨ (p1 ∧ p3)) ∨ p1) ∧ (True ∧ False))))) ∧ p4) ∨ p1))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776769490761966731959087333917 : (((p1 ∨ (((((p2 → p2) ∨ False) → ((p3 ∧ (False ∧ (p5 ∨ p1))) ∨ (p1 ∧ (p5 ∧ False)))) ∧ ((False ∨ True) → (False → p5))) → p5)) ∨ p1) ∧ True) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p2 → p2) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3205781235041699644043574188 : ((p4 ∧ p4) ∨ ((p1 → False) ∨ (p4 ∨ ((p2 → (False ∧ p1)) ∨ (((p4 ∧ ((p5 → p5) → ((p2 → p1) ∧ p4))) ∧ False) → p5))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351318602619865262198910931333 : (p4 → (((p3 → p3) → (((p4 → p3) ∨ p4) ∧ (((p5 ∧ (p5 → ((False → p2) ∨ (p3 ∨ True)))) ∨ p2) ∧ p5))) → (True ∧ (p1 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219812685009312265652129364858 : ((p3 → ((True ∧ True) ∧ True)) → ((p4 ∧ (((p2 ∨ (False → True)) → ((p3 ∧ True) → p3)) ∧ (p2 ∨ (p4 ∧ (True → p1))))) ∨ (False → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



