variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118624789661287061122327830735 : ((p4 ∨ (((False ∨ (p4 ∧ (False ∨ p1))) ∧ True) ∨ (((p1 ∧ (p1 ∧ p3)) ∧ p2) → (True → (True → (p5 ∨ (p2 → p3))))))) ∨ (p5 → p2)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h10
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216754330651426551095365340208 : ((((p1 → p2) → p3) ∧ p1) → ((((p2 ∧ (((p2 ∧ p5) → (p4 ∧ p1)) ∨ p1)) → (p4 → p2)) → p4) → (p4 ∨ (True ∧ (True ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774164696493066570063961762348 : (((False ∨ (((p3 ∨ True) → ((p2 → (p4 → (((((p4 ∨ (p3 ∨ p4)) ∨ p3) ∧ True) → (p1 ∧ p1)) → p2))) ∧ p2)) → (False ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774260654095563380256320957357 : (((False ∨ (((True → p1) ∨ (((p5 → (p4 ∧ ((p3 ∧ (p5 ∨ p1)) ∨ True))) → ((p4 → p5) ∧ p3)) ∧ p2)) ∨ (p5 ∧ (p4 → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197244053413778541979159640948 : (((((p3 ∨ False) ∧ (p2 ∧ p5)) → p4) → p3) ∨ (((True ∧ True) ∧ p5) → (p5 ∨ (p2 → ((p3 ∨ (((p1 ∧ False) ∧ p4) → p3)) ∧ False))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44307995324908087797986634624 : (((((((True ∧ (p3 ∧ ((p2 ∨ p1) ∨ ((False ∨ p1) ∨ p4)))) ∨ p4) → p1) ∨ False) ∨ (((False ∨ p2) ∨ p4) ∧ (True ∧ True))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190583330658854084758145282745 : ((((True → (p3 ∧ True)) → (True ∧ (True ∧ p5))) → p1) ∨ ((False ∧ (p2 ∨ p3)) ∨ (p5 ∨ ((p4 → ((p4 → p1) → (True ∨ p5))) ∨ p3)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148880027582200931977691693607 : (((((p2 ∧ p3) ∧ p5) → p4) ∨ ((p3 ∧ ((((p4 → p5) ∨ p4) → (p5 ∧ p1)) ∧ p5)) → (p2 ∧ p3))) ∨ (p4 ∨ (p3 ∨ (True ∨ False)))) := by
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
theorem thm_5_vars_64907542611188778401412402442 : ((p2 ∨ ((((p3 ∧ ((True ∧ p5) ∨ (p4 ∨ p5))) → True) → (((p4 ∨ (p2 ∨ p2)) ∨ True) ∧ p1)) ∨ ((False → True) ∧ (p1 → p1)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150228230476653312884176247202 : ((p2 → (True → ((True ∨ (((p2 ∧ True) ∧ False) → (p5 ∧ (p1 → (p1 ∧ p5))))) → (p2 → (p5 → p1))))) ∨ (((True → True) → True) ∧ True)) := by
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
theorem thm_5_vars_175093758970074662988033332705 : ((p3 ∧ (p5 ∨ (p4 → (((p5 → p2) → p3) → (p4 ∧ (p1 → (p4 ∨ p3))))))) → ((((p4 → (True ∨ p2)) → (True ∨ p2)) → p2) → p2)) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : ((p4 → (True ∨ p2)) → (True ∨ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h6
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : ((p4 → (True ∨ p2)) → (True ∨ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h10
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111748835681358647493987803146 : ((((p1 → ((((p4 ∧ ((p3 → ((p5 ∧ p2) → (False ∨ p4))) ∨ p5)) ∨ (False → p2)) → (p2 ∧ True)) ∨ p4)) → p3) ∨ True) ∨ (p4 ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340962536064281338969923590072 : (p2 → (((True ∧ True) ∧ ((((((p5 → False) ∧ p1) ∧ p3) ∧ p3) ∧ p5) ∨ (False ∨ (False ∨ (p1 → (p5 ∧ ((p3 ∨ p4) ∧ p2))))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112909776477732203674804660708 : ((((False ∨ p4) ∨ (p2 → ((p4 → (((p3 → (p5 ∧ p4)) ∧ ((True ∨ ((p5 → p4) ∧ True)) ∨ p5)) → False)) ∧ False))) → p1) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259571315682599744204380766801 : ((p1 → True) → ((((p3 ∨ ((p3 ∧ p5) ∨ p1)) → p3) ∨ (((p5 → p5) → (p2 ∧ p5)) ∧ (p1 ∧ p3))) ∨ (p2 ∨ (p5 → (p2 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666091858632810911473138120476 : (((((((p5 ∨ ((p5 → p2) ∧ (p2 ∧ p3))) ∨ p3) ∨ (((True → (p1 ∧ p1)) ∨ p3) → False)) ∧ (False → p1)) ∧ (False → (p4 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40463172162037848124460831622 : ((((((p5 ∨ p5) → True) ∧ ((((False ∧ ((p5 ∧ ((True → p3) ∨ p5)) ∧ p5)) ∨ p2) ∧ True) ∨ ((False ∧ p3) ∧ p3))) ∨ False) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114623285812067472771287915590 : (((((p3 ∧ True) ∨ (((p1 ∨ (p5 ∨ True)) ∨ (False ∧ p5)) ∨ (p4 → p4))) ∧ p5) ∨ ((p5 ∧ ((p2 ∨ p5) → True)) ∧ False)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115652953801648022549330843353 : (((((p5 → p1) ∨ p5) ∧ (p3 → p4)) ∨ (((((p4 ∧ (False ∧ (p4 ∧ p4))) ∧ p3) ∨ ((p2 ∨ False) ∧ p4)) ∨ p2) ∧ True)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149068499859965475800135585263 : ((((p4 ∧ p4) ∨ False) → (False ∧ ((((p3 ∨ p3) ∨ ((p2 ∨ p3) ∧ p2)) ∧ (p4 → p2)) ∧ (False ∨ True)))) ∨ (((p4 ∧ True) ∧ False) → p5)) := by
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
theorem thm_5_vars_119549780894516792708409314556 : ((p5 → ((((((p4 ∧ (True → True)) ∧ p2) ∧ (p5 ∨ ((True ∨ False) ∧ False))) ∧ True) ∨ (p2 ∨ p1)) ∨ (p4 ∨ (False ∧ False)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140746521599259069568593398145 : (((((True → (True ∧ (p5 → p1))) ∧ True) ∧ (p1 → ((p5 ∧ p5) → p4))) → ((((p3 ∨ p2) ∨ True) → p2) ∨ p3)) → ((p1 → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739126565152109412310086881736 : ((((p3 ∧ p5) ∨ (p1 → (p2 → (((((p2 ∧ p5) → p1) ∧ (((p5 ∨ True) ∧ p4) ∧ (p5 ∨ p4))) ∨ True) ∨ ((True ∨ False) → p2))))) ∨ p5) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198432435255558137954820304545 : ((p4 ∧ (p2 ∨ (p2 ∧ (p1 ∨ (False ∨ True))))) ∨ (p5 → (((p2 ∧ (((p2 ∨ p1) ∨ p3) ∨ (p2 ∧ (p3 ∧ p4)))) ∧ False) → (False ∨ p5)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h4
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h4
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338170534177788168882282890005 : (p1 → (((p4 ∨ p1) ∨ (((p3 ∧ p3) ∨ p2) ∧ p4)) → ((((False ∨ True) ∧ (((False → p5) ∧ p2) ∧ ((p1 ∨ True) → p5))) → False) ∨ p1))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
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
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148633877518306129204812014825 : (((True → (p1 → (((True ∨ p5) → (True → p1)) ∨ p5))) → ((((p5 ∧ True) → (False ∨ p1)) → False) → p4)) ∨ (True → ((False → False) ∨ p2))) := by
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
theorem thm_5_vars_739502913946047285337491642930 : ((((p5 ∧ p1) ∨ (((((p1 ∨ p3) ∧ False) → True) ∧ (True ∨ (True → p5))) → (True ∧ (p5 ∨ (p1 → (p1 ∧ (True ∧ (p4 ∧ p2)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256596496201189608293700777662 : ((p1 ∨ True) → ((p5 → (((False ∨ (((True → False) ∧ ((p1 ∧ (p3 → p3)) → p4)) ∨ p5)) → p1) ∧ True)) → ((p4 ∧ (p4 → p5)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246701503337896889174983461040 : ((p5 ∧ p4) ∨ (((p4 ∧ (p5 ∨ (p1 → ((True → True) → True)))) → (p5 → p4)) → (((p1 → p4) ∨ (p5 → (True ∧ p5))) ∧ (True ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670482566543343174115179655880 : (((((p2 ∨ p4) ∧ (p1 → ((((((p2 → p1) ∧ (p5 ∨ p3)) ∨ p4) ∨ (p1 ∨ (p2 ∨ p4))) ∧ False) ∨ p1))) ∨ (False ∨ (False → p1))) ∨ p1) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174528734804757130750873803363 : (((((p2 → p5) ∨ (p1 ∧ p2)) → p3) → (((True ∧ (p4 ∨ False)) ∧ True) ∨ True)) → (((((p2 ∨ p1) ∧ p2) ∧ p3) ∨ (p4 ∨ True)) ∨ p4)) := by
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
theorem thm_5_vars_345595834890142399991771070077 : (p3 → (((p4 → p3) ∧ ((((p5 ∨ (p4 ∧ p5)) ∨ p3) → ((p2 ∧ p1) ∨ ((((p3 → p1) → p5) ∨ p1) → (p4 → p3)))) → p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_815896352936235553662877050 : ((p2 ∧ (p2 → (((((((True → p1) ∧ p3) ∧ ((False ∨ p2) ∧ False)) ∨ True) ∨ (p1 ∨ p2)) → p3) → (p2 ∧ (p5 ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694049433001262087203608068649 : ((((((p4 ∧ (p4 ∧ False)) ∧ (True ∧ (False ∨ p4))) ∧ (p2 ∧ (p2 ∨ True))) ∨ ((((True ∧ p3) → (p4 ∧ p5)) → (False → p5)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115028160137955177834082820281 : (((False → ((((p2 → (p2 ∧ False)) ∧ True) → (p5 ∧ p3)) → p4)) ∧ (True ∧ ((p2 ∨ p1) → (((p2 ∧ p3) ∨ p2) → False)))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117871727331668281118698257032 : ((p5 ∧ ((p5 ∧ ((((p2 ∨ p3) → True) → p3) ∧ ((((True ∨ ((p1 → p1) → p3)) ∨ p4) → p2) ∨ (p1 ∧ p5)))) ∨ False)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689428774176982031530445567670 : ((((((p3 ∧ (False ∧ (True ∧ p1))) ∧ ((p2 ∨ True) → p5)) ∧ (p5 ∧ (True → True))) ∨ (((((p2 ∨ p5) ∨ p1) ∧ p1) → p1) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338069442861822467320943868576 : (p1 → ((((p2 ∧ (p3 ∨ True)) ∨ p5) ∨ (p5 → (True ∨ p5))) → (((True ∧ (p3 → p1)) ∨ (p3 → (False ∧ True))) → (p1 → (p3 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
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
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167062013591907279964890609730 : ((((p4 ∧ (((False → p5) → (((p4 ∨ True) → p1) → (p4 ∧ p3))) ∨ p4)) ∨ p5) ∨ p5) → (((p2 ∧ (p3 ∧ p3)) ∧ (p2 ∧ p1)) → p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h4.left
  let h10 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
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
        exact h8
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h18 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_561398205174063688608308789 : (((p5 ∨ ((((p3 ∨ (p1 ∧ (p1 ∧ (p4 ∧ False)))) ∧ ((p2 → p1) ∨ p4)) ∧ p3) ∨ ((p3 → p1) ∨ (p3 ∧ p2)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175300577457094764578062465590 : ((p3 ∨ (p5 ∧ (((p2 ∧ (p4 ∨ False)) ∨ False) ∨ (((p5 ∨ p4) ∨ p5) → False)))) → (p5 ∨ (p5 ∨ (p3 → ((p1 ∧ (p2 ∨ p5)) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
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
          exact h5
        case inr h12 =>
          -- False on the left can always be used.
          apply False.elim h12
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169102100949318059698827693532 : ((p4 → (((p1 → (False → False)) ∨ p1) ∧ (((p4 ∧ p1) → ((p1 → p5) ∧ p2)) ∨ p3))) → (((True → p1) → (p4 → (p2 ∨ p3))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : (p4 ∧ p1) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260028798303226577815437288699 : ((p2 → True) → (p2 → (((((((p1 ∨ p5) ∧ ((True → p1) ∨ p4)) ∧ (p3 ∨ (True → (p2 ∨ True)))) ∨ False) ∨ (p5 ∨ p3)) ∨ p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142729993547764785092712859035 : ((p2 ∨ (((p2 ∨ (p2 → ((False ∧ p3) ∧ p2))) → ((True ∨ p1) ∧ (True ∧ p1))) ∨ (((False ∨ p3) → True) ∨ p3))) → ((p5 ∧ p1) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
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
theorem thm_5_vars_118429428724868186374136507316 : ((p2 ∨ (p4 ∨ (p2 ∨ ((((((p4 ∨ ((p4 → p1) → p5)) ∧ p4) ∧ (p2 ∧ ((p4 ∨ p5) → p1))) ∧ p1) ∨ p3) ∨ p4)))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338357021587813206427035431264 : (p1 → ((((p1 ∨ p1) → True) → p2) ∨ ((p4 ∧ (((((p4 ∧ (p4 → p1)) ∧ False) ∨ (p3 → True)) → p4) ∧ ((p4 → True) ∨ True))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52009273981580786601598476945 : (((p3 ∧ ((True → (((p1 ∨ p5) → p1) ∧ ((p5 → False) ∧ p2))) → (True → p4))) ∨ (p2 ∨ (((p4 ∧ (p2 ∨ p3)) → p2) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168325253109764808635396312409 : (((p3 → True) ∧ (((True ∧ ((p1 ∧ p4) ∧ False)) ∨ ((False → p1) ∧ (p3 ∨ p4))) ∨ p1)) → (((p2 → p5) ∧ (p5 ∧ p3)) → (False ∨ p5))) := by
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
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649303002306818618274393820271 : (((((False ∨ (((p2 ∧ ((((p2 ∧ p1) ∨ p3) → (p2 → p2)) ∨ ((p5 ∧ (p1 → True)) ∧ p5))) → p1) → p1)) → p5) ∧ (False → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752348878953547154816697803580 : (((False ∧ (((p1 → (((((False ∨ True) ∧ p3) ∨ (p2 → p5)) → ((True ∧ (True → p3)) ∧ ((p2 → p3) ∨ p1))) ∧ False)) ∨ p4) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64297983519424733951994988258 : ((False ∨ (p4 → ((p5 ∧ ((p1 ∨ p4) ∨ False)) ∨ ((((True ∧ (p2 ∨ p4)) ∨ (p5 → p3)) ∧ (p4 ∨ (p4 → p2))) ∧ (False ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115880072793257000337499481263 : ((((True → (p2 ∧ p5)) ∧ p4) ∨ ((((p5 ∧ (p5 → (p3 ∧ p2))) ∧ ((True → ((p2 → p5) ∧ p1)) → False)) ∧ p3) ∨ True)) ∨ (p2 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214247158967779165850686791389 : (((p1 ∧ (True ∧ p2)) → False) ∨ ((((p2 ∨ (p5 ∧ (p1 → p2))) → ((p4 → p1) ∧ p1)) → p4) → (((True → (p2 ∨ p5)) → False) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 ∨ (p5 ∧ (p1 → p2))) → ((p4 → p1) ∧ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h7 : (True → (p2 ∨ p5)) := by
        -- Implications on the right can always be decomposed.
        intro h8
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h7
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h13 : (True → (p2 ∨ p5)) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h15 := h2 h13
      -- False on the left can always be used.
      apply False.elim h15
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h16 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h17 : (True → (p2 ∨ p5)) := by
        -- Implications on the right can always be decomposed.
        intro h18
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h19 := h2 h17
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h23 : (True → (p2 ∨ p5)) := by
        -- Implications on the right can always be decomposed.
        intro h24
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h25 := h2 h23
      -- False on the left can always be used.
      apply False.elim h25
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h26 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59003521959306522442811135400 : (((p3 ∧ p2) ∨ (((p1 ∨ (p4 → (p2 ∨ (False ∨ (p3 → ((True ∨ False) ∨ (False → p4))))))) → p2) → (p4 → ((p5 ∨ True) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65191474369831853976474674825 : ((p3 ∨ ((p5 ∨ ((p2 ∧ ((True ∨ p3) ∧ ((True → (False → (True ∨ (p1 ∧ ((p4 ∧ p4) ∧ (p4 ∨ p4)))))) → p1))) → p5)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338784431624730645201375368367 : (p1 → ((p4 ∧ p4) ∨ (((p4 ∧ ((p2 ∨ False) ∨ p3)) ∨ (((p5 → (True ∨ False)) ∨ True) ∧ True)) ∨ (p2 → (((False ∨ p5) ∧ True) ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85950920463005965110597019886 : (((((False ∨ (p4 → True)) ∨ (p2 ∨ (True ∨ p4))) → p5) ∧ (p5 ∧ ((((p1 → p4) ∧ (True ∧ (p5 → p2))) ∧ (True ∧ p4)) → p4))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749799800956596913497741395300 : (((True ∧ ((True ∧ ((False ∨ p5) ∨ ((p1 → (p5 ∧ False)) ∨ (False ∧ (((p4 ∧ (((p3 ∨ False) ∧ p4) ∨ p5)) ∧ False) → p2))))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186503026607444877915024810829 : (((p4 ∨ (((p1 ∧ (False → False)) → True) ∧ p2)) ∧ (p5 ∨ True)) → ((((p1 ∨ p4) ∨ (p5 → (p4 → (p5 ∨ p5)))) ∨ p5) ∨ (False ∨ p3))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41445497782498641220023785381 : ((((p2 → (False ∧ (((False → (((False → False) → p2) → p1)) ∨ True) ∧ p5))) → ((((True ∨ (True ∧ p4)) ∧ p5) → True) → p1)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142852236404116416303601620550 : ((p4 ∨ ((False → (True ∧ (((p2 ∧ (False ∨ p3)) ∨ p4) ∧ ((p5 → ((True ∧ False) ∧ (False → False))) ∨ p4)))) → p5)) → (p1 ∨ (p4 ∨ p5))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (False → (True ∧ (((p2 ∧ (False ∨ p3)) ∨ p4) ∧ ((p5 → ((True ∧ False) ∧ (False → False))) ∨ p4)))) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h5
      -- False on the left can always be used.
      apply False.elim h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167789658663750459718999413180 : (((True ∨ (((p3 ∨ (p3 ∧ False)) ∧ (p4 ∧ p4)) ∧ (True → True))) → (True ∧ (p3 ∧ p2))) → ((((p5 ∨ p1) → p1) → p5) ∨ (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133929044553919624796049887554 : (((p5 ∨ (p3 → (((True ∧ True) ∧ (p4 → (p1 ∨ p4))) → ((((p5 → (True ∨ p3)) → True) → p1) → False)))) ∧ p3) ∨ ((True ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116900145889527428670381465018 : (((p4 → p5) ∨ ((p4 → (p4 ∨ (p2 → (p2 → p1)))) → (((p1 ∨ (p5 ∧ p2)) ∧ p5) → ((p5 → (False ∧ p1)) ∨ p5)))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181628711650485667387264984594 : ((p2 → (p4 ∨ ((p3 → (p1 ∨ p2)) ∧ ((p4 ∧ (p2 ∧ True)) → False)))) → (((False → (p3 ∨ ((p5 ∨ p3) → False))) → (False ∧ p1)) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → (p3 ∨ ((p5 ∨ p3) → False))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115986895889661102129879777129 : ((((p2 → (p5 ∧ False)) ∨ p5) → ((p1 → p3) ∧ (p2 → (((p1 ∧ p1) ∧ False) ∨ (((False ∨ (False ∧ p1)) ∧ False) → p1))))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746717766330224628427612108593 : ((((p3 ∨ p2) → (p5 ∧ ((((p1 → ((True ∧ (p2 ∧ True)) ∧ False)) ∧ ((p4 ∨ (p1 ∨ False)) ∨ (p1 → p2))) ∨ (False ∧ p5)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60725065754241626419016572195 : ((True ∧ ((p4 ∧ (p1 ∨ (p2 → False))) ∧ (p5 ∧ (((True ∨ True) ∧ (p3 → ((p1 ∨ (False → (p2 ∨ p3))) ∨ (p4 → p2)))) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226854137317577623673619555056 : (((p4 ∧ p4) → p5) ∨ ((p2 ∧ p4) ∨ ((((p1 ∨ p4) ∧ (((((p2 ∨ p4) → (False → p1)) ∨ (p1 ∧ p1)) ∨ True) ∧ p1)) ∨ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347757794245588568733681310009 : (p3 → (((p4 → False) ∧ p4) ∨ ((((True ∨ p5) ∧ (p5 → ((p5 → (False ∨ p3)) ∧ p1))) ∧ ((p2 ∧ p2) ∧ (p5 ∧ p4))) ∨ (False → p5)))) := by
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
theorem thm_5_vars_145752642618578332065166774043 : (((p3 ∧ p2) ∨ (((p2 ∧ (True ∧ p2)) ∧ ((((p1 ∧ p4) → (p5 → p5)) → (p5 ∧ p4)) ∧ p3)) ∨ True)) ∧ (True ∨ (p1 → (False → False)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339808702407693067259267810969 : (p1 → (p5 ∨ ((p2 ∧ ((p3 → ((False ∧ p5) → p2)) → (p2 → p3))) ∨ ((((p4 ∧ ((p3 → p1) ∨ (p1 ∨ True))) → False) ∧ False) ∨ p1)))) := by
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
theorem thm_5_vars_720170278100853059299354263974 : (((((False ∨ (p5 ∨ p4)) ∧ p5) → (p5 → (((p2 ∧ (p3 → p1)) ∨ (((p1 ∨ False) → (True ∨ ((False → p2) ∨ p2))) ∨ False)) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677270493433726281665660696514 : (((((((p5 ∧ p2) ∨ p5) ∧ (p4 ∨ ((p3 → p3) ∧ ((p4 ∨ False) ∧ ((True ∧ p3) → False))))) ∧ p3) ∨ ((True ∨ p5) ∨ (p4 → p2))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39233644905336855571242379343 : (((True ∧ (p4 → ((((True ∨ ((p1 ∧ p5) ∧ False)) ∧ p2) → (p1 ∨ p5)) ∨ (p2 ∨ ((p1 ∨ p2) ∨ ((p5 ∧ False) ∨ p4)))))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749682126442311003588963187186 : (((True ∧ (((False ∨ (((p2 → True) → False) ∧ (p1 → ((True → (False ∧ (((False ∨ p1) → True) → p4))) ∨ True)))) ∧ (p5 ∧ p5)) ∨ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_340860214394091762912807498772 : (p2 → ((((((((p5 ∧ p2) ∧ p3) ∨ (p3 → p2)) → (p5 ∧ p5)) → False) → ((p1 → p3) ∨ p5)) ∧ (p5 ∨ (p5 → (p3 → True)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712036649988558750881015306162 : ((((((p4 ∧ p1) ∨ (False ∨ p2)) ∨ p2) ∨ (True ∨ ((p3 ∨ p1) ∨ ((((p1 ∧ True) → p3) ∧ (p3 ∧ (p1 ∨ (p4 → p1)))) → p5)))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_314662805983582194293816302642 : (p3 ∨ ((p3 ∧ ((((True → False) ∧ (True ∨ False)) ∧ True) ∨ (((p4 ∧ True) ∨ p3) ∨ p1))) ∨ (p5 → ((False ∧ ((p2 ∨ True) → p1)) → True)))) := by
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
theorem thm_5_vars_265645825099948129948009056193 : (True ∧ (p2 ∨ (((((((False → ((False ∨ p4) → False)) ∨ p3) ∧ p3) ∨ p5) ∨ True) → (p3 → (p4 → (p3 ∧ (p4 → p2))))) ∨ (p1 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_774394297229044424380498725948 : (((False ∨ ((((p1 ∧ ((((p3 ∧ p1) ∧ p3) → p1) → False)) ∧ True) ∨ (((p2 → True) ∨ p3) → p4)) → (p5 → ((p3 ∧ False) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355607244443976784860809694066 : (p5 → (((p1 → p3) ∨ ((((p3 → p3) ∧ p1) ∧ p5) → (((p1 ∨ ((p5 ∨ p3) ∨ p3)) ∧ (p1 → p5)) → (False ∨ p4)))) ∨ (p2 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47439155666525790606270915706 : (((p3 ∧ ((((True → (((((False ∨ (False ∨ False)) → (p3 → True)) ∧ True) ∨ p3) ∧ p2)) → (p5 ∨ p5)) ∨ p3) ∧ False)) ∨ (p3 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51754556249957479813061998481 : ((((p5 → p2) ∧ (((p1 ∨ True) ∨ ((((p1 ∧ p4) → p3) ∨ p3) ∧ p5)) ∨ False)) ∧ ((p4 ∨ p1) → ((True → p4) ∧ (p5 ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115386351769657803031239397628 : ((((p1 ∨ p5) ∧ ((p3 ∨ False) ∨ (p4 ∧ True))) ∧ ((((p3 ∨ True) ∨ False) ∨ p2) → ((p1 ∨ ((False ∧ p1) ∨ p5)) ∨ p1))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759069892700039628414228018035 : (((p2 ∧ ((p3 → (p5 → (((((p4 ∨ p4) ∧ (True ∧ (p1 → p2))) → p2) ∧ p3) ∨ ((False ∨ ((p4 ∨ p1) ∧ p1)) → p5)))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133846938648488089107263989344 : (((True ∧ (p4 ∧ ((p3 ∨ ((p5 ∨ (((p2 ∧ False) → False) ∨ True)) ∧ ((True ∧ (p3 → p5)) → True))) → False))) ∧ True) ∨ ((True ∧ p3) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114719895854408064410875678012 : ((((((False → p3) ∧ (p4 → p5)) → ((p3 ∨ p2) → (p5 ∧ p3))) ∨ (p3 → p3)) → ((p4 → p4) → (p1 ∨ (p3 ∨ p5)))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699763740646456110212475118847 : ((((((p3 ∨ (p4 → (p3 → (p2 ∧ False)))) ∨ p3) ∨ (p1 ∧ p5)) → ((p3 ∨ True) → (((False ∧ (p5 ∨ p2)) → p3) → (p2 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40535404348950123393272845878 : ((((p2 ∨ (False ∨ (p3 ∨ ((False ∨ ((((p2 ∧ p1) ∧ (p4 → ((p3 → p5) ∧ p5))) ∧ (p5 ∧ p3)) ∧ p4)) ∨ True)))) ∨ p4) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148013382422483783747675323688 : ((((p2 ∨ ((p3 ∨ False) ∧ ((p2 ∧ ((False ∧ p2) ∧ False)) ∧ p3))) ∨ ((True ∧ False) ∧ p5)) ∨ (False → p3)) ∨ (((p2 ∧ p4) → False) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245003385993026860333112851459 : ((p1 ∧ p4) ∨ ((False ∧ (p1 ∧ (((p4 ∨ p3) → p4) → p5))) ∨ (False → (p2 ∧ (((p5 ∨ p5) ∧ (p4 → (False ∨ (p1 → p1)))) ∧ p5))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125028762518630320913368150492 : ((((False ∧ p1) → False) ∧ (True → ((((((p3 → True) → True) ∨ (((p5 → p2) ∨ (True ∧ False)) ∧ False)) → p1) → p4) ∧ p5))) → (p4 ∨ True)) := by
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
theorem thm_5_vars_740643912122111271758696783046 : ((((p2 ∨ p2) ∨ ((p1 ∨ ((p4 ∧ ((p2 ∨ p2) ∧ (False → p4))) → p2)) ∧ ((p2 → (((False ∧ True) ∧ False) ∨ (p3 → p2))) ∨ False))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h9
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299323802078722372489922158537 : (False ∨ (((((False → p4) ∨ p1) ∨ p4) ∧ ((p5 ∧ (p5 → ((True → (p5 → p1)) ∨ (p2 → p3)))) ∧ (False ∨ ((True → p3) ∨ p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54143021403571251871402258002 : (((True → (((p4 ∨ p1) ∨ p4) ∧ ((p5 ∨ p4) → p2))) → (p5 → (p4 ∧ (p4 ∨ (False → (p4 ∨ (p4 → (p3 ∧ (True → True))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57733743154365865390433634066 : ((((p3 ∨ p2) → p1) → (((p3 ∨ (((p2 ∨ p4) ∨ False) → (p4 → p5))) → ((p3 → (((p1 ∨ p3) ∨ False) → p2)) → p2)) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65739036624746077023043154031 : ((p4 ∨ ((((p4 ∧ p2) ∧ (False ∧ ((p4 → p1) ∨ (p3 ∧ (p1 → (((p2 ∨ True) → False) ∨ True)))))) ∧ p4) ∨ (p1 → (False ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219233587050380636661168190866 : ((p1 ∨ ((p1 ∨ p3) ∨ False)) → ((((False ∧ ((p1 ∨ (False ∧ p1)) ∧ ((p3 ∧ p2) ∨ p1))) ∨ (p4 ∨ ((p4 ∨ p2) ∧ p5))) ∨ p4) ∨ True)) := by
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
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207214528461275034634764364500 : ((((p1 → (p5 ∧ p3)) ∧ False) ∨ True) → ((p5 ∧ p5) → (((p2 ∧ p5) → ((((True ∨ (False ∧ p5)) ∨ p5) ∨ p1) ∧ (p4 ∨ p4))) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



