variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50429758304626285201436117013 : (((p5 ∧ ((p1 ∧ ((p3 → (((p3 → p3) → (False ∧ (p4 → p3))) ∨ (p3 ∧ False))) ∧ p5)) ∨ p5)) ∨ ((True → (p5 ∨ p4)) → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356740764764149334964528927472 : (p5 → ((p5 ∧ (((p2 → p3) ∧ p3) → p1)) ∨ (((p1 ∨ (((p3 ∧ (False ∨ (p2 ∧ (False ∨ True)))) ∧ (p4 → True)) ∨ p3)) ∧ p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42087412628786047536891956071 : ((((p4 → p1) ∨ ((((p5 ∨ p4) → (p1 ∨ p3)) ∧ (p3 → ((((p5 → p4) ∧ p4) → (p5 → (p5 ∨ p1))) → p2))) ∧ p5)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750236047373242313366438770955 : (((True ∧ ((((((p3 ∧ ((((p3 ∨ ((False ∨ p5) → p4)) → False) ∨ p1) ∨ False)) ∨ True) → (p1 ∨ True)) → p4) ∨ True) ∨ (p4 ∨ False))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40324161013271176839716946902 : (((((((((p3 → p3) → p1) ∨ (True ∨ (True ∨ p4))) → (p4 ∨ (((p5 ∧ (True → True)) ∧ p4) ∧ True))) ∧ False) ∨ p2) ∨ p5) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133609948228243368216997836104 : (((((((True ∨ p5) ∨ ((True ∨ p1) → (((p4 ∧ (p1 ∨ p4)) ∨ p4) → p2))) → True) ∧ (p4 → p4)) → p4) ∧ p1) ∨ (p4 → (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180998743145699419016099919882 : (((p5 ∧ p1) ∨ ((True ∧ (((p5 → (p1 → p5)) ∨ p3) ∨ p2)) → p1)) → (((((p3 ∨ p4) ∨ p4) ∨ (p5 ∨ p2)) ∧ p5) ∨ (p2 → True))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733866384981601683470827048916 : ((((p5 ∧ p5) ∧ (((((p1 → ((p4 ∨ ((((p3 ∨ p3) ∧ p5) ∧ False) ∨ True)) ∨ False)) ∧ (p1 → p5)) → p1) ∨ p4) ∨ (p4 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703211496617757284769023645884 : ((((False ∧ (p4 ∧ (False ∨ ((False ∧ True) ∧ (p1 → p1))))) ∨ (((p5 → ((p1 ∧ (p1 ∧ p2)) → ((p5 ∧ False) ∨ p1))) ∧ p4) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_305003198622290598373981245768 : (p1 ∨ (((p1 ∧ (p3 ∧ (((p3 ∨ p4) ∨ (p3 → (p4 ∨ p2))) → (False → p4)))) ∨ (p4 → ((p2 ∨ p3) ∨ p4))) ∨ ((p5 → p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134887624622570134942527766867 : (((p4 → (((((p5 → (p5 ∧ (False ∧ p4))) ∨ p1) ∧ (p2 ∧ (p1 ∧ p4))) → (p4 ∨ (p1 → p3))) → p5)) → p4) ∨ ((True ∨ p3) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199142931949234241955696331940 : ((((True ∧ True) ∨ ((p5 ∧ p3) ∧ p2)) ∧ p2) → (((((p3 ∨ (p4 ∧ (False → p4))) ∧ (p4 ∨ True)) ∨ (True ∨ True)) → (p5 ∧ False)) ∨ p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50354715171011399896049623090 : ((((p4 ∨ ((p2 ∨ p4) ∨ p4)) ∨ ((False → ((p4 → (p1 ∧ ((p2 ∨ p2) ∨ p3))) ∨ False)) → p5)) ∨ ((True ∧ p4) ∨ (False ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172878703151146028428440101609 : ((p1 ∧ (((True → (True ∧ p5)) ∧ (p4 ∧ False)) ∨ ((p5 ∨ False) → (p1 ∧ p1)))) ∨ (p2 → ((((p3 → True) ∧ (p2 → p2)) → p1) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42221474667967220016418186642 : (((False ∧ ((((p2 ∨ (True ∨ p1)) → (p3 ∨ (True → (((p1 ∧ p4) ∧ p5) ∧ (p3 ∧ (p5 → p3)))))) → p3) ∧ (p1 ∨ True))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230275691993478687497358047666 : (((False ∨ p4) ∧ p2) → (((p1 ∨ (p5 ∧ (((False → p1) ∧ True) ∧ ((((p2 → p4) → p4) ∧ False) ∧ (False ∧ False))))) ∨ (True → p4)) ∧ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338542606912630264916048355746 : (p1 → ((p4 ∧ (True ∧ p5)) ∨ (p2 → (((p5 ∧ (p1 → ((p1 → p5) → p5))) ∧ p3) ∨ (p2 ∨ (p2 ∨ (((p2 → p1) → p2) ∧ p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44391377417754652726060756829 : (((((p1 ∧ p4) ∧ ((p2 ∨ p5) → ((True ∧ (p2 → p2)) ∧ (False ∨ p5)))) ∨ ((p4 → p1) ∧ (((p5 → False) ∨ p4) ∧ p4))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306686788128816801978959544780 : (p1 ∨ (True ∧ (p5 → ((((p2 → ((p4 → p4) ∧ ((p2 → ((p5 ∨ p1) ∨ ((False → (p4 ∧ p3)) → p4))) ∨ p5))) → p3) ∨ p1) ∨ p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321538053396112795223027012561 : (p4 ∨ (p2 → ((True ∧ (p2 ∧ (False ∧ (False ∧ ((False ∧ ((p4 ∨ False) ∨ True)) ∧ (False → ((True ∧ (p1 ∨ p1)) ∨ (p5 ∧ p3)))))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589349584035848374970761529251 : (((((((((p3 ∧ p4) ∨ True) ∨ (((((p5 ∧ (p2 ∨ (p3 ∧ p5))) ∨ p1) ∨ p1) ∧ (p4 → p5)) ∧ p2)) ∨ p4) ∨ p2) → p1) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110794812486558015361982700742 : ((((((((True → True) → (p5 ∧ ((p5 → p5) → (p1 → ((p3 ∧ p5) → p5))))) ∧ p5) ∧ p2) ∧ (p2 ∨ p5)) ∨ p4) ∧ p2) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51893694096550527545379357848 : (((((p5 → p5) ∧ ((True → False) → (False ∧ (p4 ∨ (p2 ∨ (p5 ∧ p1)))))) → p5) ∨ ((p5 ∨ p1) → (True ∨ (p2 ∨ (False → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226126968485757160586773556423 : (((False ∨ p1) ∨ p3) ∨ (((((False ∧ p2) → (p4 ∧ ((True ∧ p1) ∨ (p1 ∨ p1)))) ∨ False) → p4) ∨ (True ∨ (((p5 ∧ p2) → p2) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112030677862468285826225035117 : (((((p5 ∨ p2) ∨ p1) ∨ (((p4 → (((p2 ∨ True) → p3) → ((p2 ∨ p5) ∧ True))) ∨ ((False ∧ True) → True)) ∨ True)) ∨ p3) ∨ (p3 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227744960518133910419563180976 : ((p1 ∧ (p2 ∨ p1)) ∨ ((p4 ∨ (p3 ∨ False)) ∨ ((False ∨ (((p3 ∨ p1) ∧ False) ∧ p5)) → ((True ∧ (True ∨ False)) → ((p1 → p2) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h12
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147274944318785563267430046122 : (((((p5 ∨ ((p5 → p3) → (p1 ∧ p1))) ∧ (False ∧ ((((True ∧ False) ∧ p5) → True) ∨ False))) ∨ p1) ∨ True) ∨ (p1 → ((True ∨ p1) ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50949117814111993520990597918 : ((((((False → p3) ∨ True) → ((False ∧ p1) ∨ False)) ∨ (p2 ∨ (p3 ∨ ((p5 ∧ p5) → p4)))) ∧ ((False ∧ (p2 ∨ (p1 → True))) → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148395574725203730901011506157 : (((p4 ∧ (p4 ∨ ((True → (p3 → (p4 ∧ (p1 ∨ True)))) ∨ (p4 → p1)))) ∨ (p2 → ((p5 ∧ True) ∨ p2))) ∨ (p2 ∨ (False ∧ (False ∧ False)))) := by
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
theorem thm_5_vars_322557590450179007139151354104 : (p5 ∨ ((p1 ∨ ((True ∧ p4) ∧ (p1 ∧ ((p3 → (((p1 → ((p2 → True) → (True ∨ p4))) ∧ p1) ∨ (True ∧ (False → False)))) ∨ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300102226563989096603150269211 : (False ∨ (((((p5 → (((p4 → (p2 ∧ (p5 ∨ False))) ∨ False) → False)) → p5) ∨ True) ∨ (True ∨ (((True → p4) ∧ False) ∨ p1))) ∨ (p2 → p1))) := by
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
theorem thm_5_vars_189685644421774766889302548765 : ((p3 ∨ ((((p4 → (p4 ∧ True)) ∨ p4) → p3) ∨ True)) ∧ ((p5 ∧ (((p4 ∧ (p4 → ((p4 ∧ p5) → (True ∨ p5)))) → p1) ∧ True)) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355751930082720680706164023898 : (p5 → ((True → ((p5 ∧ (p2 ∧ ((p5 → (p4 → p3)) ∨ p5))) ∧ (p5 ∧ (p2 ∧ (((p2 → p5) ∨ p5) → (False ∧ p1)))))) → (p1 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : ((p2 → p5) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h11
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
  have h16 : ((p2 → p5) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h15, we can now drive its conclusion.
  let h17 := h15 h16
  -- We need to get the right conjuct of h17 based on <expert-advice>.
  let h18 := h17.right
  -- One of the premise coincides with the conclusion.
  exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233218465737578980527561823549 : ((p5 ∧ (p2 → p4)) → (((((((p4 ∧ False) ∧ True) ∨ (((p3 ∧ (p5 ∨ p1)) → p3) → p4)) ∨ p4) → p2) ∧ p4) ∨ ((p4 ∨ p2) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746817201666913064038220791614 : ((((p3 ∨ p5) → ((p2 ∨ (p1 ∨ (p2 ∧ ((((((p2 ∧ True) ∨ p3) ∧ p5) → p1) ∨ ((p3 ∧ False) ∨ p5)) ∧ p3)))) ∨ (True ∨ p1))) ∨ p1) ∧ True) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225809444148394096195006996488 : (((True ∧ p1) ∨ False) ∨ ((p3 ∨ (((p3 ∧ p2) ∧ (((p3 ∧ (p5 ∧ (p1 → (p1 ∨ p2)))) → (p3 → (False → p2))) ∨ False)) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618908209162105974024341042440 : (((((p3 → (p2 ∧ p4)) ∧ ((p2 → p3) → ((p3 ∧ ((False ∧ p5) ∧ p3)) ∧ (False ∨ (p1 ∧ ((p3 ∨ p3) → (True ∨ p3))))))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800879612055607841623099210145 : (((p2 → ((False ∨ (p1 → (True → ((p2 ∨ ((p1 ∧ (p3 → p2)) ∧ (p5 ∧ ((p1 → p3) ∧ p2)))) → (False ∨ False))))) ∨ (True ∨ p4))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48894088078185563452815261434 : (((p2 → ((p3 ∧ (False ∨ (p1 → (False ∨ (p5 → p5))))) ∨ (((p1 ∨ True) ∧ (True ∨ p1)) ∨ (p4 → p1)))) ∧ ((p3 ∨ True) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42401523270673751555978915735 : (((p4 ∧ (p2 ∨ (((p4 ∨ (False ∨ p3)) ∨ p1) ∧ ((p4 → (True → True)) → ((p3 → (True → p1)) → ((p4 ∨ p1) ∧ False)))))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1571981069660431907325783685 : ((p5 → (((p3 → p5) → (((True → ((p2 ∨ (p3 → (p1 ∧ p5))) → True)) ∨ p2) → (p3 ∧ True))) ∨ (p1 ∨ p5))) ∨ (p3 ∧ p1)) := by
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
theorem thm_5_vars_47434523245657731436985964028 : (((p2 ∧ (((p1 → p5) ∧ p2) ∧ ((True → (True ∧ p2)) ∧ (p4 ∧ (True ∧ (((True ∨ p4) → p4) ∧ (p1 ∨ p4))))))) ∨ (False → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622982045183339287865388290671 : ((((p5 ∧ (((p2 → p1) ∨ p2) ∨ (((((True ∧ True) ∨ ((p1 → p5) ∧ p1)) ∧ ((p4 ∧ (p4 → p5)) ∨ p5)) → p4) ∧ True))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740922606256013186027685193818 : ((((p3 ∨ p2) ∨ (((p5 ∨ (p2 ∧ p1)) ∧ True) ∨ ((((((False → False) ∨ True) → True) ∨ (p5 ∨ (p4 → (p5 ∨ False)))) ∨ p1) ∨ p4))) ∨ p1) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53149761306141653035625975851 : ((((((((p2 ∧ False) → p1) ∨ (p2 ∨ True)) ∧ p5) → p2) ∨ p5) ∨ (p2 → (((p2 → p1) ∨ (p5 ∧ (p1 ∧ (p2 ∨ p4)))) → True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179094512027786395893706988898 : ((False ∧ (((False ∧ (p3 ∨ (False ∨ (p4 → p4)))) → (True ∨ p2)) → p4)) ∨ ((False → (False ∨ p2)) ∨ ((p3 → p4) ∧ ((p4 → p5) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191068449590048184943596682793 : (((p4 ∨ (p2 → (False ∧ p4))) → (p4 ∨ (True → False))) ∨ (p3 → ((True ∨ p3) ∨ (((p2 ∨ False) → (p3 ∧ ((p1 → False) → p5))) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686020428531027341670196497212 : ((((((((p3 → (False → p2)) → (p5 → (p3 → (p1 → True)))) ∧ p5) ∧ p4) → (p3 → p2)) → (False ∧ ((p3 ∨ True) ∨ (p2 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164450760204158582215799690741 : (((((((p2 ∨ p3) ∨ True) ∨ (False ∨ p3)) ∧ ((True ∨ p1) ∧ (True ∧ False))) ∧ p4) ∧ p1) ∨ (p5 ∨ (True ∨ ((p3 → False) ∨ (False ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192698631701911033122516802115 : ((((((p3 ∨ p4) ∧ p1) → p5) → (True ∧ p5)) → p1) → ((((p2 → True) ∧ ((p1 ∧ p3) ∧ ((p5 → True) → p2))) ∨ True) ∨ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342475575647603866158160801216 : (p2 → ((((False ∧ (p4 ∨ (p2 → p1))) ∨ (p3 ∨ (p4 ∧ (p1 ∨ p2)))) ∨ p3) ∨ (False → ((False → (p2 ∧ p2)) ∧ (p4 → (False ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318894968675337206432610470861 : (p4 ∨ ((p3 ∧ ((p4 ∧ ((((True ∧ ((True ∨ p3) → (True → p3))) ∨ p3) ∨ (p1 ∧ (p2 ∧ True))) ∧ p1)) ∧ p2)) ∨ (False ∨ (p1 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102596927089593330152347118363 : (((((((p5 ∨ ((p3 → p2) ∨ (p5 ∨ p1))) ∨ ((p5 → (p3 → (p4 ∨ False))) ∨ (p1 ∨ p5))) → p5) ∧ p1) ∧ p3) ∨ True) ∧ (False → False)) := by
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
theorem thm_5_vars_93728820736694786096905445285 : ((p1 ∧ ((p2 → ((((p5 ∧ (False → (p2 ∧ False))) ∧ (p5 ∨ (p1 ∨ p2))) ∨ (((p4 ∧ True) ∧ p1) ∧ (p2 ∨ p3))) ∧ False)) ∧ p2)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246277247405863534540561387715 : ((p4 ∧ p4) ∨ (((True → (p4 ∨ ((p4 → True) → False))) ∨ (p5 → p4)) ∨ ((True ∧ True) ∨ ((p3 ∨ (p4 ∧ False)) → ((p5 ∨ p5) ∨ p5))))) := by
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
theorem thm_5_vars_55215745963566172105437873692 : (((((p5 ∧ p4) ∨ p2) ∨ (p3 ∧ p3)) ∨ ((((p2 ∨ (p1 → p3)) ∧ p1) ∨ False) ∨ (((True ∧ (p4 → p1)) → True) ∨ (p1 ∧ p5)))) ∨ p1) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124295019833211140221864754244 : (((((p5 → True) ∨ ((p4 ∧ True) ∨ False)) → False) ∧ (p1 → (((p4 ∧ (False ∨ (p4 ∨ ((p5 ∨ p2) ∨ p4)))) ∨ False) → p4))) → (p5 ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 → True) ∨ ((p4 ∧ True) ∨ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301374460681858897870206946024 : (False ∨ (((False ∨ (True ∨ p1)) → False) ∨ (p3 → (((True ∧ (((p4 ∨ p5) ∧ p1) ∧ p5)) ∧ ((((p2 → p2) → p3) → p4) → False)) ∨ True)))) := by
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
theorem thm_5_vars_176586780491092457984957735931 : ((((False → p3) ∨ (False ∨ (p2 → p2))) → ((p5 ∨ (True ∨ p2)) ∨ False)) ∧ ((p5 ∨ ((True → p1) → p5)) ∨ (False ∨ ((True ∨ p5) ∨ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
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
theorem thm_5_vars_673297496622733494139260639321 : (((((((False → p1) ∧ ((True → False) ∧ p1)) ∨ p3) → ((False → (True ∧ p5)) ∧ (((True ∧ False) ∧ False) → p4))) → (p4 → (True → p4))) ∨ p3) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50902904213225307421109650502 : (((((p5 → (True ∨ p2)) ∨ ((p1 ∧ True) → ((p2 ∨ (p3 → False)) ∨ p5))) ∧ (p1 → p5)) ∧ ((False ∧ ((p1 ∨ p2) ∧ p1)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41145621769282781859188329394 : ((((((p4 → p2) ∨ ((p5 ∧ True) → (p1 ∨ p4))) → (p2 → (True ∧ (((p4 ∨ p2) ∨ p5) ∧ p2)))) ∨ (p3 ∧ (p3 → p1))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134913111416051137863070718330 : ((((((p5 ∨ False) ∨ ((((True ∨ p3) → ((p5 → (p2 → p5)) ∧ p2)) ∨ p4) ∨ False)) ∨ True) ∨ True) ∧ (False ∧ p5)) ∨ ((True ∧ False) → p2)) := by
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
theorem thm_5_vars_746721475273994914961214076486 : ((((p3 ∨ p2) → (p5 ∨ (((((((p4 ∧ p2) → (p5 ∨ p4)) → p2) ∧ (p4 ∧ p5)) ∧ ((True ∧ p4) → p5)) ∨ False) ∧ (True ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238101705665637333493061665603 : ((True ∨ p2) ∧ (p4 ∨ ((((True ∧ ((p4 ∨ p4) ∨ p1)) → False) ∧ p1) → (p3 → ((p2 ∧ p2) ∨ (p5 ∧ ((p4 ∧ (True → p1)) → p4))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (True ∧ ((p4 ∨ p4) ∨ p1)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119314880158307424718197328149 : ((p3 → (((((p1 ∨ (p1 ∨ False)) → (((p3 → p2) ∧ p2) → (p4 → p5))) ∨ (False → p1)) ∧ p1) → (p2 ∨ (p5 ∨ p3)))) ∨ (False ∨ p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51168810713272237290544194861 : ((((((False ∧ False) ∨ (p2 ∧ ((p4 ∧ (p2 ∧ p5)) ∨ (p2 ∨ False)))) ∨ True) ∨ (p5 ∧ p5)) ∨ (p2 ∧ (p1 → ((p3 ∧ False) ∧ p5)))) ∨ p2) := by
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
theorem thm_5_vars_248048310782288812327792617161 : ((p1 ∨ p5) ∨ ((False ∧ p5) ∨ (p4 → ((True → ((p2 → False) ∨ (((((p4 ∨ p5) ∨ p4) ∨ True) → p3) → (p3 → True)))) ∨ (p3 ∧ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246330395804921843577465953277 : ((p4 ∧ p5) ∨ ((((((False ∨ True) → p4) ∧ (((p5 → p2) ∨ ((False ∧ True) ∨ p4)) ∨ (True ∧ p5))) ∧ True) ∧ p5) → (p3 → (p1 ∨ p4)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h11 : (False ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h12 := h7 h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- False on the left can always be used.
        apply False.elim h15
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h21 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h22 := h7 h21
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354748662081620746039113381060 : (p5 → (((((p2 ∧ p3) ∨ (p3 ∧ ((p2 ∨ ((p4 ∨ (False ∧ p3)) ∧ p4)) ∨ True))) ∨ True) → (p2 ∧ ((p1 ∨ p5) → (True → p2)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668107043280599058134152618604 : ((((True → (p2 ∨ (p5 → ((True ∨ p2) → ((p5 → p3) ∧ ((((p4 ∨ p2) ∨ p3) ∨ True) ∧ (p5 → True))))))) ∧ (p2 → (p5 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164480333569508558601221546730 : ((((p4 ∧ (p4 → (False ∨ ((p5 ∨ (True ∨ ((p4 → False) ∧ p1))) ∧ True)))) ∨ False) ∧ p4) ∨ (((p5 ∧ (p5 ∧ (True ∧ False))) → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788776803672078814297748939994 : (((p5 ∨ ((p4 ∧ (((((p4 ∨ (False ∨ (p1 ∨ False))) → (p1 ∨ ((p4 ∨ p1) ∧ p3))) → (p4 ∧ (p2 ∧ p2))) → p3) → p5)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347839943056562491606713730571 : (p3 → (((True ∨ p4) → p2) → (((((p5 → p3) → p5) ∧ (p3 ∧ ((p4 ∧ ((p4 ∧ p5) → p2)) ∧ (p3 ∨ (p1 ∨ True))))) ∨ p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315786242168154391468181626760 : (p3 ∨ ((p4 ∧ p3) → (((p5 → False) ∨ ((p4 → (((p2 ∨ (False ∧ ((((True ∨ p2) → p4) → True) → p2))) ∧ p3) ∨ p1)) ∧ p1)) ∨ p4))) := by
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
theorem thm_5_vars_63335093370460675149180350654 : ((p5 ∧ ((p1 → True) → (p4 ∧ (False ∨ ((p4 ∧ (((((True → p2) ∨ False) ∧ (((p3 → p2) → p5) → p3)) ∧ p3) ∧ p3)) → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351518829968499708814993830199 : (p4 → ((((((p3 ∨ p2) ∧ False) ∧ ((True ∨ p2) ∨ ((p5 ∧ (p1 ∨ p5)) → p3))) ∧ p5) ∨ p5) ∨ (((p4 → (p3 → p1)) ∨ p3) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737634885772988315717836797895 : ((((p5 → p3) ∧ (((((p4 → p3) ∨ (True ∧ False)) → p5) ∧ (((p4 → p5) ∧ p3) ∨ (p3 ∧ ((p3 ∨ p1) → (p2 ∧ p5))))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182004707275709447017051524898 : ((((((p2 ∨ (p1 ∧ False)) → p1) ∧ p3) ∨ (False → False)) ∨ p1) ∧ (True ∧ (p4 → (p1 → ((p2 ∧ ((True → p2) ∨ (p5 ∧ False))) ∨ p4))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9106621531974946196895341930 : ((((((p5 ∧ ((p5 ∧ (p2 ∨ p5)) ∧ (True → True))) ∨ p2) ∧ p5) ∨ (p4 ∨ (False → (False → ((p1 ∨ p3) ∨ (p1 → p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809387356390361112451577475706 : (((p5 → ((p5 → ((((p4 ∧ p1) → (p2 → ((p3 ∨ False) ∧ ((p1 ∧ p3) → True)))) ∨ (p5 ∧ p1)) → (p4 ∧ (True ∨ True)))) ∨ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54594332500024829663468073388 : (((True → (((True ∨ False) ∨ True) ∧ (p2 → False))) ∨ (((False ∨ ((p1 ∨ True) ∨ ((p4 ∧ ((p4 → p2) → False)) ∨ p3))) → False) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256871999045346078644092985747 : ((p1 ∨ p3) → (p3 → (((p4 ∧ (p2 ∧ (p1 ∧ (p2 → p1)))) ∨ True) → ((((True ∧ False) ∧ p1) ∨ (p2 ∨ (p1 → (p3 ∨ p4)))) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347415561120663546189374282010 : (p3 → (((False → p5) ∧ (((True → p2) → False) ∨ p3)) → ((p1 ∧ (p3 → (((p1 ∧ (p2 → p5)) ∧ (False → (p1 ∧ p1))) ∨ True))) ∨ p3))) := by
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
theorem thm_5_vars_33023144362789206801376237526 : ((p3 ∨ ((((p1 ∧ (p3 ∨ (p2 ∨ p3))) ∧ p5) ∨ p4) → ((p3 ∧ p3) ∨ (False → ((p2 ∧ True) → ((False → p1) ∧ (p3 ∨ p4))))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h7
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h12
        -- False on the left can always be used.
        apply False.elim h12
        -- Conjunctions on the left can always be decomposed.
        let h13 := h11.left
        let h14 := h11.right
        -- False on the left can always be used.
        apply False.elim h10
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h15
        -- One of the premise coincides with the conclusion.
        exact h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h17
    -- Implications on the right can always be decomposed.
    intro h18
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h19
    -- False on the left can always be used.
    apply False.elim h19
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- False on the left can always be used.
    apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190717826596450499224878086388 : ((((p4 → (True → True)) ∧ (False → p4)) ∧ (p3 ∨ p5)) ∨ ((((p1 ∧ (False → p4)) ∨ (p4 → (p2 → (p1 → (p4 ∨ False))))) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111473620018785063280904545449 : (((p1 → (((p3 → (True ∧ p5)) ∨ p2) ∨ (((p3 ∧ (p1 ∧ ((p2 ∨ p4) ∨ p2))) ∨ ((True ∨ p5) ∨ p4)) ∨ p1))) ∧ False) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662252217728996151329036541661 : (((((p2 ∧ (p5 → (p3 ∧ (p4 → ((p2 → p2) ∨ p4))))) ∨ ((p1 → ((p5 ∧ p4) ∧ ((p1 ∧ p4) ∨ p4))) → p3)) → (p1 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136682853853034971061834739053 : (((p2 → (p3 → p1)) → ((p4 ∧ p5) ∧ (p4 → ((((((p5 ∨ True) → p1) ∨ p1) → p1) ∧ p2) ∧ (p2 ∨ True))))) ∨ ((p1 ∨ p1) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170965691927501722491760878258 : ((p2 ∨ ((((p5 → (False ∧ (False → False))) ∧ ((p4 ∧ False) ∧ False)) ∨ p4) ∨ True)) ∧ ((p4 ∨ (p2 ∨ True)) ∨ (((False ∨ p5) → p3) ∧ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_194723028533168628980223984901 : (((True ∧ (p2 ∧ (p2 → (p4 ∨ p4)))) ∨ True) ∧ (False ∨ ((p1 → (p3 ∨ p3)) ∨ (((((p3 → p4) → False) ∧ p4) → (p5 ∧ True)) ∨ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p3 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354582534269229814367886036080 : (p5 → (((((p3 ∧ p4) → p4) → (((((p5 ∧ (p4 ∨ p5)) → p4) ∧ (False ∧ p3)) ∨ p5) ∧ ((True ∨ (False ∧ False)) ∨ p5))) ∧ p5) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300878841835790643770688144949 : (False ∨ ((((False ∧ p1) ∧ (True ∧ p3)) ∧ ((p4 → p5) ∧ ((True ∨ False) ∨ p3))) ∨ (((True ∧ ((p2 ∨ p3) ∧ (p3 → p1))) → p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171353086331168223756865999637 : ((((p5 ∨ (p1 ∨ (((p1 ∧ (p4 → (False ∨ p3))) ∨ False) → p1))) → p1) ∧ p2) ∨ (True ∨ ((((p4 ∧ (p1 ∧ True)) ∧ True) ∧ True) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205396968529651972701329297239 : ((((False ∨ p3) → p5) → (p2 ∧ False)) ∨ ((True ∨ True) → (True ∨ (False ∨ (((((p5 ∨ p4) ∨ (p4 ∧ False)) ∧ False) → (p5 → p3)) ∧ True))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161949936003840440504796079964 : ((p2 → (((True → p4) ∧ ((p2 ∨ p1) ∧ ((((False ∨ p3) ∨ True) ∨ p2) ∨ p2))) → (p4 → p1))) → ((p4 ∨ True) ∨ ((p5 ∨ p3) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337124246272855534670467436223 : (p1 → ((p2 ∧ ((((p2 ∧ p1) ∨ p2) ∧ ((p3 ∨ False) ∨ (p2 ∧ (False ∧ p4)))) ∧ (((p4 ∨ (False ∧ p2)) → p5) → p3))) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133745572202551277358349105709 : ((((((True → ((p1 ∧ p3) ∨ p2)) ∧ p2) ∧ False) ∨ (((p3 → p5) → (p3 → p3)) → ((p1 ∧ False) ∧ p1))) ∧ p4) ∨ (False → (p3 ∧ p2))) := by
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
theorem thm_5_vars_219916664474649261392275490218 : ((p4 → (p2 ∧ (True ∧ p5))) → (((p1 ∧ p4) ∨ ((False ∨ ((p2 → p5) ∧ (((p4 ∨ p1) ∧ False) → False))) ∧ (p1 → p2))) ∨ (False → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2770183009200017548253832719 : ((((False → p2) ∧ p3) ∨ p4) ∨ ((((p2 ∧ (p2 ∨ ((p2 ∧ False) ∧ (p4 ∨ (False ∧ (p5 ∧ p4)))))) ∨ True) ∧ (False → False)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



