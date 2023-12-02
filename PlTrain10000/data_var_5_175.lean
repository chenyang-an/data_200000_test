variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149931665390430359235358104222 : ((p3 ∨ (((p5 ∧ (True ∨ p5)) → p3) ∨ (p3 ∨ (p1 → (p5 ∨ (((False ∨ False) → False) ∨ (False ∨ False))))))) ∨ (((p1 ∧ p4) ∨ p1) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319641065666399663914717118374 : (p4 ∨ ((((p2 → False) ∨ False) ∧ (False ∨ (p1 ∨ False))) ∨ ((p1 → True) → (p1 → (False → (p5 ∧ (((p5 ∨ p4) → p1) ∨ (True ∧ True)))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44805194877467614585355811570 : (((((p3 → p1) → False) ∧ ((p1 ∨ (True ∨ ((p3 → (p5 → p5)) → (False ∨ (p2 ∧ False))))) ∧ ((p3 ∧ p5) ∨ (p2 → p2)))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146967777900470048035200137049 : (((((((p3 → (p3 ∨ True)) ∨ p4) ∨ ((p5 → ((p2 ∨ (p2 ∨ p2)) → p5)) → False)) ∨ p2) → False) ∧ p2) ∨ (p3 ∨ ((True ∧ p3) → p3))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345462108024391525844632480882 : (p3 → (((p1 → (p2 ∧ ((True ∨ p1) → ((False ∧ True) ∨ (p5 ∨ ((p3 ∧ (p2 → (p1 ∨ (p4 ∨ True)))) ∨ p1)))))) → (p1 ∧ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118739439160209562106093695304 : ((p5 ∨ (((p5 ∨ p3) ∨ ((p4 → (p1 ∧ p2)) → p4)) ∧ ((False → p3) → (p1 ∨ (p3 ∧ ((p2 → p2) ∧ (p1 → p4))))))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337559194259302151062921495842 : (p1 → ((p1 → (True → (p4 → (p3 ∨ ((p2 → p5) → (((True → p5) → (p2 ∧ p2)) ∨ (True → p4))))))) ∨ (((p1 ∧ p2) ∧ False) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54723755569872960774484079508 : (((((p4 ∧ p2) → p1) ∧ (p3 ∧ (True ∨ p2))) → ((p4 ∨ p4) ∨ (p2 ∨ (True ∨ ((((p4 ∧ p3) ∨ p1) → (p4 ∨ False)) ∨ p3))))) ∨ p2) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61185392840933673526098242624 : ((False ∧ ((p4 ∨ True) ∧ ((p4 ∧ (p5 ∧ (p5 ∧ (False ∨ p2)))) ∧ ((False ∨ p3) ∨ (True → ((False ∨ p1) ∨ ((p3 ∨ p4) ∧ p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148695365930870838441027911531 : (((True → (p1 ∨ (((False ∧ False) ∧ p2) ∧ False))) ∨ ((False → ((True ∧ ((p1 → p5) ∨ p3)) ∨ True)) ∨ p4)) ∨ ((p2 ∧ (True ∧ False)) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186868405735757111397591368342 : ((((False ∨ (True ∨ p5)) ∨ p3) → (p5 ∧ (True → (p1 ∧ False)))) → (((((p1 ∧ True) ∨ p4) → (p5 → (True ∧ (p1 ∨ False)))) → p3) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∨ (True ∨ p5)) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : ((False ∨ (True ∨ p5)) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h13 := h11 h12
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356284736413060994964127876822 : (p5 → ((((p3 → ((p4 → False) ∨ ((p3 ∨ ((p4 → True) ∧ p3)) ∧ p4))) ∨ p4) → True) → ((p5 → (((p3 ∨ True) ∧ False) ∧ p3)) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119583195027015940365858991943 : ((p5 → ((p1 → p4) ∧ ((p4 ∨ True) ∧ (p5 ∧ ((p4 → p4) → (((p2 ∨ p1) ∧ ((p5 → p4) → (p3 → True))) ∧ False)))))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135354803085391305948558635000 : (((p2 ∨ ((p3 ∧ (p5 ∧ (p4 ∨ ((False ∧ ((p4 ∧ p5) ∧ (p2 ∨ p1))) ∧ False)))) → False)) ∧ (p4 ∧ (p1 ∧ p2))) ∨ ((True ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110896178506518294146086029747 : ((((((p4 ∨ p4) → p5) ∧ (((p5 ∧ ((p3 ∨ ((p1 → p4) ∨ True)) ∧ p2)) ∧ (False → (p1 ∨ p1))) ∧ True)) → p3) ∧ False) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321251801471080560588394760993 : (p4 ∨ (p4 ∨ ((p2 ∨ (False ∧ (p4 → (False ∧ (p3 ∧ (((p1 → p1) → (p3 → True)) → p2)))))) ∨ (False → ((False → (p1 ∨ False)) → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164446320750211903176515922971 : ((((((p2 ∧ (p2 → p1)) → ((p3 ∨ p5) ∧ (False ∨ (False ∨ p1)))) → p3) ∧ False) ∧ p3) ∨ (((True → (True → p3)) ∨ p4) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254159991584168359949877831188 : ((p2 ∧ p1) → ((((True ∨ p1) → (((((p1 → ((p3 ∨ p5) ∨ p4)) ∨ p1) → p1) ∨ (p4 ∨ p5)) ∨ (p5 ∧ p1))) → p3) ∨ (p5 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51082451925072930320365212659 : (((p5 → ((p4 ∨ ((((p5 ∨ True) → p4) ∧ False) ∧ False)) ∧ ((p1 → (False ∧ p4)) ∧ p1))) ∧ (p5 ∨ ((p3 ∧ (p1 ∨ p5)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338555231801068096017911385081 : (p1 → ((p5 ∨ (False ∧ p1)) ∨ ((p3 ∧ p5) ∨ (False ∨ (False ∨ (((((p4 ∨ (p4 → (p5 ∧ False))) → (p4 → p2)) ∨ True) → p4) → p4)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p4 ∨ (p4 → (p5 ∧ False))) → (p4 → p2)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358159411741958867707344222038 : (p5 → (p3 ∨ ((p3 → (p4 ∨ ((p5 → p5) ∧ (True → ((((((True ∧ p4) ∧ (False ∨ True)) → p4) → (p3 ∧ p4)) ∨ p4) ∨ p3))))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111836756282368473648984428803 : ((((((True → (p5 ∧ False)) ∧ ((False → (False ∧ (p5 → p3))) → p1)) ∨ ((True ∧ p4) ∧ p3)) ∨ ((p1 ∨ True) ∧ False)) ∨ p4) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135678226513727610576066933611 : (((((((p4 ∧ ((p3 ∨ (p3 → p4)) → p1)) → True) → p2) ∨ False) ∧ p2) ∧ (((p2 ∨ (True ∨ False)) ∧ p1) ∧ p3)) ∨ ((p3 ∧ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148649168130434670291727873438 : ((((p1 ∨ ((p2 ∨ True) ∧ p1)) ∨ (p2 ∧ False)) ∧ ((p4 ∧ False) ∨ (((p5 → p4) ∨ (True → p2)) ∧ p4))) ∨ (((p4 ∧ p5) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305633463356408768377912297756 : (p1 ∨ ((p3 → ((p4 → p2) → (p1 → (((p1 ∨ True) → p2) ∧ p5)))) → (p4 ∨ (True → ((p2 ∨ ((True ∨ p5) ∨ False)) → (p4 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
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
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207142337744790788986980246001 : (((False → (p4 ∧ (p1 ∨ p5))) ∧ p4) → (False ∨ ((((p5 → (True → ((False ∧ (p3 ∨ (p3 ∨ p1))) ∧ (p4 ∨ p1)))) ∧ p3) ∨ False) → p4))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785576249553354168004442920888 : (((p4 ∨ ((p4 → ((((((p1 ∧ ((p5 ∨ p2) → ((p4 → (p1 ∧ (p4 ∧ p1))) ∧ p3))) ∧ p1) ∧ True) → p5) → p1) ∧ True)) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_304314512263240839040718085941 : (p1 ∨ (((((p4 ∧ p1) → p3) ∧ (p3 ∧ ((p4 ∧ ((p1 ∨ True) ∨ (p3 → p3))) → p5))) ∧ ((((p2 ∨ p2) ∧ True) ∨ False) → p3)) → p3)) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52252953945413926255262931065 : (((p1 ∨ ((p4 ∨ (p1 → p4)) ∧ ((True → True) ∧ ((p3 → False) ∨ (p4 ∨ False))))) → (((True → p3) → (p5 → p1)) ∧ (p4 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_437000857286552103017240038257 : ((((True ∧ (((((p1 ∧ (p5 ∨ (p5 → p4))) ∨ ((p3 ∨ True) ∨ (p5 ∧ ((p5 ∧ p1) ∨ True)))) ∧ True) → p4) → p2)) → (p2 → p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673582872482676650183886575680 : ((((((False → False) ∧ True) ∨ (((p1 ∧ (p2 → ((p1 → p3) → (True → False)))) ∨ False) → ((True ∨ p1) ∨ False))) → (p3 → (p5 ∨ p3))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230724907930682268484188456478 : (((p5 → False) ∧ p1) → ((((True ∨ p3) → False) ∧ (p1 → (p5 → (((((False ∨ p2) ∨ p3) → False) ∧ ((p1 ∧ False) → p5)) ∨ p1)))) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191749993402672498606499536783 : ((False ∨ (p3 ∧ (True ∧ (((p3 → p2) ∧ p1) ∧ p5)))) ∨ (p4 → ((p1 ∨ (((p3 ∧ p4) → p4) → (p4 ∨ p2))) ∨ ((p1 ∨ p5) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54812491507423667529608986428 : (((p3 ∨ (p4 ∨ (p1 ∧ (True ∨ (p4 ∨ False))))) → ((p4 ∧ (p1 ∧ ((True ∨ (p5 ∧ ((p2 ∨ False) ∧ p4))) → p1))) ∧ (p2 → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169075584077205309989441259294 : ((p3 → (True ∧ ((True ∧ (((p1 ∧ ((False → p2) ∧ (True ∧ False))) → p3) → True)) ∧ p4))) → ((((p3 ∧ p2) ∧ True) ∨ (p1 ∨ True)) ∨ p4)) := by
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
theorem thm_5_vars_716212659702442258921122354097 : (((((p2 ∨ (p1 ∧ p1)) → True) ∧ (((False ∨ ((p3 ∨ (p4 → ((False ∨ (p4 ∧ p5)) ∨ p1))) ∨ p2)) ∧ p2) ∨ ((p3 ∧ p1) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612471269354127476018415256308 : ((((((((p2 ∧ p4) ∨ p5) ∧ ((p5 → p2) ∨ ((p5 ∧ p2) ∨ ((p4 ∨ ((p4 ∨ False) ∧ p4)) ∨ True)))) ∧ p2) ∨ (True ∨ p1)) ∨ p5) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_135237818018437119990088848533 : ((((p3 ∧ (p3 ∧ p2)) ∧ (True ∨ (p4 → (((p4 ∨ p4) ∨ (((p5 → False) ∧ p1) ∧ True)) ∨ p3)))) → (p2 ∧ False)) ∨ ((p4 → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39639368897496794367208803536 : (((p3 ∨ (((False → (p2 ∨ ((((True ∨ (((p3 ∧ p2) → (p5 ∧ False)) → True)) ∧ p2) ∨ p5) → p5))) → p4) ∧ (True → p2))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258946358044707062650715333144 : ((True → p3) → ((((((p1 ∨ (p4 ∧ p1)) ∨ (p1 → p3)) ∧ (p4 → p3)) → (True → ((p4 → True) ∨ (False → p2)))) → (p5 → p3)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117287526331354187084125496724 : ((False ∧ ((((((p3 ∨ p3) ∨ p4) ∨ ((p2 ∧ True) → p4)) ∨ (p1 ∧ ((False → p5) → True))) ∧ ((p2 ∨ True) ∨ p3)) → False)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119815036766582179880199994459 : ((((((p3 ∧ p3) ∨ (p2 ∧ (p5 ∧ (False ∧ (p2 → p5))))) ∨ (((p4 ∧ p2) → (p3 ∨ (p5 ∨ True))) ∨ p4)) → False) ∧ p5) → (True ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p3 ∧ p3) ∨ (p2 ∧ (p5 ∧ (False ∧ (p2 → p5))))) ∨ (((p4 ∧ p2) → (p3 ∨ (p5 ∨ True))) ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308744066602685870660712385134 : (p2 ∨ ((p4 → (((p4 ∨ True) ∨ ((False ∨ p4) ∨ (p1 → p3))) → ((True ∧ False) ∨ (False → (((p3 → p4) ∧ False) ∧ (p4 → False)))))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h5
      -- False on the left can always be used.
      apply False.elim h5
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h5
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h9
      -- False on the left can always be used.
      apply False.elim h9
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h9
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h17
        -- False on the left can always be used.
        apply False.elim h16
        -- False on the left can always be used.
        apply False.elim h16
        -- Implications on the right can always be decomposed.
        intro h18
        -- False on the left can always be used.
        apply False.elim h16
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h21
      -- False on the left can always be used.
      apply False.elim h20
      -- False on the left can always be used.
      apply False.elim h20
      -- Implications on the right can always be decomposed.
      intro h22
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255243991719766068539563808427 : ((p4 ∧ p5) → ((True ∧ (((p1 ∧ (p4 ∧ p4)) ∧ (p4 ∧ (True ∨ p1))) ∧ (p4 ∧ (((p3 ∨ (p4 → False)) ∨ (p3 → p4)) → p3)))) ∨ p4)) := by
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
theorem thm_5_vars_213756850086331749622310270562 : ((((p4 → p3) → False) ∨ p2) ∨ (p5 → ((p1 ∧ p2) ∨ (((p5 → (p1 ∨ p5)) ∨ ((p3 ∨ p5) ∨ p5)) ∨ ((p3 ∧ p3) → (p5 ∧ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682402576646398782868288385133 : (((((p4 ∨ ((False → (p1 ∨ ((p5 ∨ (p3 → False)) ∧ (p3 → False)))) ∧ p1)) → (p2 → p5)) ∧ ((p3 → p1) → (p2 ∨ (p5 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251145573903132447562869154955 : ((p2 → False) ∨ ((p1 ∧ p3) ∨ (((p1 ∨ False) ∧ (False ∧ p3)) ∨ (((p2 ∧ (p5 ∨ (p3 ∨ (p3 → (True → True))))) ∨ (False → p4)) ∨ p1)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55419108114268025167949315813 : ((((True ∧ (p2 → (False ∧ False))) ∨ p2) → ((p3 ∨ ((p2 ∧ p3) ∧ ((((p5 → ((p3 ∧ True) ∧ p4)) → p5) ∧ p1) ∧ True))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348814554890533519258495453933 : (p3 → (p1 ∨ (((p1 → (False → p3)) → (p1 ∧ False)) ∨ (p5 ∨ ((True ∨ (p4 ∧ ((p3 ∨ (p1 ∧ p3)) ∨ (p3 ∧ (p4 ∨ p2))))) → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45983218491371683128783223222 : ((((((p2 ∧ ((p1 ∨ (True ∨ (False ∨ ((p1 ∨ (p2 ∨ p4)) → p4)))) ∨ p1)) ∧ ((False → p5) ∨ False)) ∨ p1) ∧ True) ∧ (p5 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151502432890382528269348086627 : (((((p1 ∧ True) ∧ p1) ∨ (True ∨ ((((p3 → True) → p4) → ((p2 → p5) ∧ p3)) → False))) ∨ (p1 ∨ p4)) → (((p5 ∧ False) ∧ p3) ∨ True)) := by
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
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
theorem thm_5_vars_216693226028529503057250953241 : ((((p5 → p5) ∨ False) ∧ p1) → ((False ∧ ((True ∨ (((True → p1) ∧ True) → p4)) ∧ (p2 ∧ (p3 → False)))) ∨ ((p5 ∧ (p1 ∨ p1)) ∨ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785338350934045040075117125609 : (((p4 ∨ ((((True → (p2 ∨ (((((p1 ∨ p2) ∧ (p2 → True)) ∧ p5) ∨ p1) → (p1 ∧ ((p3 ∧ p4) ∧ p5))))) ∨ p4) ∨ True) ∨ p5)) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55589132142207181567370895109 : (((p3 ∨ (p5 ∧ (p2 → (p3 → False)))) → ((((p1 ∧ (False → ((p3 → p4) → p1))) → (p4 ∧ p5)) ∨ (p3 ∧ p1)) ∨ (True ∨ p3))) ∨ p3) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592947962664351022568179247901 : (((((p1 ∨ ((True ∨ (p3 ∨ (p4 ∨ (((True → p4) ∧ (p2 ∨ (p4 ∧ p1))) ∧ p3)))) ∧ (p1 ∨ p3))) ∧ ((p2 → p1) ∨ p5)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696300264394531854165427093922 : ((((p1 → ((False ∧ (True ∧ (p4 → (p1 ∨ (p1 ∨ (p1 → p4)))))) → True)) → (((p3 → p2) → p5) ∧ (p3 → (p4 ∧ (p5 ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645866811515984127758999263772 : ((((True → ((p2 ∧ (p4 ∧ (((p4 ∧ p3) → p1) ∨ ((p4 → False) ∨ (((p2 ∨ (False ∨ p4)) ∧ p3) → (p1 ∧ p2)))))) ∧ False)) → False) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147799434740773425052868281923 : (((p1 ∧ ((((p4 → (p2 → p2)) ∧ p4) → (p4 ∨ (True ∨ p5))) ∨ (((p3 → p5) ∨ p4) ∨ p2))) → p2) ∨ (True ∨ (p5 → (p5 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339517572092061584955531972722 : (p1 → (False ∨ ((p2 → p5) → (((True ∧ ((p3 → (p4 ∧ p5)) → p5)) ∧ (p4 ∧ ((p5 → ((False → (True ∧ False)) ∧ p3)) ∨ p5))) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723729007364084316181477707684 : (((((False → p4) → False) ∧ (((p3 ∨ ((p1 ∧ True) ∨ p4)) ∧ ((p4 ∨ p1) → (p1 ∧ p5))) ∨ (True ∨ ((True → p2) ∧ (p3 → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_396216514478324653812985081831 : ((((p4 ∧ (p1 ∧ (p1 ∨ (p4 ∨ ((p5 ∧ (p4 ∨ (p5 ∨ (p2 ∨ p5)))) ∧ (((((p5 ∨ p1) ∨ p5) ∧ p4) → True) → False)))))) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722286418801594418746048778179 : (((((False ∧ p3) ∧ p2) ∧ (p1 ∧ ((((False → p5) ∧ p2) ∨ p2) ∨ ((False → (((p2 ∨ p1) ∨ p3) ∨ ((True → p4) ∧ p4))) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614746136810049613855823229893 : (((((((p5 ∨ (((p5 → p1) ∧ p5) ∨ p3)) → ((False ∧ p5) ∨ p5)) → ((True ∨ True) ∧ p1)) ∨ ((p1 ∨ p4) ∨ (p5 ∧ p2))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_184960231709504011541806350221 : ((((p5 ∨ p4) → p1) → (True ∧ ((p5 → p3) ∧ (True → p4)))) ∨ (True ∧ (True → (((p1 ∨ p5) ∧ (p2 → p4)) ∨ (p3 → (False → False)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168450452764456402149401234689 : (((False → p1) → (((False → p1) ∨ p4) ∧ (((p2 ∨ p4) → (p2 ∧ (p5 → p5))) ∧ False))) → (p5 → (((p4 → p2) ∨ p3) ∧ (True → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (False → p1) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (False → p1) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h9
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50231827740060994216662813127 : ((((((p5 ∧ ((True ∨ (p5 ∧ (p3 ∨ (True ∧ ((True ∨ False) ∧ p2))))) ∨ True)) → False) ∧ p1) → p5) ∨ ((p4 ∧ p2) → (p2 ∨ False))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51900136993775649760209426424 : ((((False → (p1 → ((False → ((p4 ∧ p4) ∧ p4)) → (True ∧ (p2 ∧ True))))) → p4) ∨ (p2 → ((p3 ∧ True) → (False ∨ (True ∨ True))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205494600013548184954108080790 : (((p2 ∧ True) ∧ (True → (p3 → p5))) ∨ (((((False ∨ (True → (True ∧ (((p1 ∨ p2) ∧ p3) ∨ p1)))) ∧ (p2 → False)) ∨ p3) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186129403892458127862885224673 : ((((False ∨ (False ∧ (p4 ∧ p4))) → ((p3 → p1) ∧ True)) ∨ True) → ((p1 ∧ (p2 → (((p3 → p2) → p2) ∧ p2))) ∨ ((p5 ∧ p1) → p5))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179039265134009626910789872421 : (((True → p4) → (((p4 ∨ (p5 → ((p4 ∨ p3) ∧ p2))) → p4) → p1)) ∨ (p4 → (p2 → ((True ∨ ((True ∧ (False ∨ p2)) ∨ p5)) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192828070020158943566823129875 : (((p5 → ((p2 → p4) ∨ ((True → p1) → True))) → False) → ((((False ∨ p5) → ((p3 ∨ ((True ∨ p1) ∨ (False → False))) → p3)) ∧ False) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → ((p2 → p4) ∨ ((True → p1) → True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178396841862151260152662941317 : (((((p3 ∨ False) ∨ False) ∧ ((p4 ∧ (p5 ∧ False)) → p3)) → (False ∧ p3)) ∨ ((False ∨ False) ∨ (p3 ∨ ((True ∧ True) ∨ (False → (True ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_347101519763207130952412394868 : (p3 → ((((p5 ∨ ((p4 ∨ p1) → (p1 ∨ p3))) → ((p5 ∧ False) → False)) → p5) ∨ (((p3 ∨ p5) ∨ (p2 ∧ (p5 ∨ (False ∧ p2)))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661156846214855210550609028078 : ((((((((p2 ∨ True) ∨ (True ∧ ((False → p1) → p4))) ∧ (p5 → ((p1 ∧ (p3 ∧ p2)) ∨ p3))) → False) ∨ (p1 ∧ p4)) → (p1 → p1)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156646942364706244360342479227 : (((((((((p3 ∨ ((p5 ∧ p1) ∨ (p2 ∧ p2))) ∨ False) → False) ∨ p3) ∧ p3) → p1) → False) ∧ p1) ∨ (p1 ∨ ((True → (False ∧ p2)) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147398787221985380104253295028 : ((((p3 ∧ (((False ∧ True) ∧ p1) → p2)) ∧ ((((p3 → p5) ∧ p3) ∧ p2) ∧ (p1 ∧ (False ∧ p1)))) ∨ True) ∨ (p5 → (p1 ∧ (p1 → p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674551748933490707700698291217 : ((((True → ((((((p1 → p4) ∧ p4) ∨ (p3 → p1)) → (p2 ∧ p1)) ∨ (True ∧ ((p4 → p5) ∧ p3))) ∧ p3)) → (p3 ∨ (p2 ∧ p1))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111554561379416781482410277434 : (((((((p5 ∨ False) ∧ (False → p1)) → ((p4 ∧ p4) ∧ (p2 ∧ (p3 ∨ p3)))) ∧ ((p4 ∧ (p4 → p5)) ∧ p1)) ∧ True) ∨ True) ∨ (True → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57338854523746260469682531882 : (((p1 ∧ (p5 → p5)) ∨ ((((((p4 → ((p5 → (p3 → p5)) → True)) ∧ p2) → (p4 ∧ ((p2 ∨ False) ∧ p4))) → p2) ∨ p2) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675377860323792062256766049530 : (((((((p5 → (p3 ∧ (((p1 ∨ p2) → True) ∨ p2))) ∧ (p1 ∨ p3)) ∨ (p4 ∨ (p5 → p2))) → p2) ∧ (((p2 ∧ True) ∨ p4) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595988498398994854439410440043 : (((((p3 → ((True → (p4 ∨ True)) ∧ (p2 ∨ (p5 ∨ False)))) ∨ ((((True ∨ (p4 → p1)) ∨ (p2 → p1)) ∨ p3) ∧ (p1 ∨ p5))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117129467482155927227950618623 : (((p4 → p4) → (((p2 ∨ ((False → ((p3 ∧ True) → p1)) ∧ ((p5 ∧ (((p2 ∧ True) ∨ True) ∧ p3)) → p5))) ∨ p1) → p2)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171995466680312215322599235072 : ((((((p5 ∨ p2) → False) → ((p2 ∨ p1) ∨ (True → p5))) ∨ True) ∨ (True → p5)) ∨ (False ∨ (p2 → (p4 ∨ (p3 ∧ (p3 → (False ∨ p4))))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64247430542078846939674103611 : ((False ∨ (p2 ∨ ((True ∧ (p1 → (p2 → p3))) → ((p2 → (p3 ∨ False)) ∨ ((p5 → (False ∨ (p1 ∨ False))) ∨ ((True → False) → p1)))))) ∨ p3) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56723389461856307035813756061 : ((((p1 ∨ p2) ∨ False) ∧ (((p2 ∧ p2) → ((p1 ∨ (True ∧ p3)) → ((((False ∧ p5) ∧ True) → ((p4 ∨ p5) ∧ p2)) ∧ p4))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65979601562483497351325959012 : ((p4 ∨ (p1 → ((((p5 ∧ ((p5 ∧ False) ∧ p1)) ∨ p1) ∧ (p4 → (p5 ∨ ((p1 → (True → (p1 → (p2 ∨ p3)))) ∧ p3)))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157692917680672112221579145854 : ((((((p2 ∨ ((p4 ∧ False) ∨ False)) → ((True ∧ False) ∨ p2)) ∧ p5) ∧ p5) → (p1 → (p4 ∨ False))) ∨ (p5 → (((p5 → p4) ∨ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234084876154111674132050272007 : ((True → (p2 ∧ p4)) → (p1 → (((p1 → ((p4 ∧ p1) ∧ ((((p1 ∨ (p5 → (True ∧ (p1 ∨ p2)))) → p2) ∨ p5) ∨ p1))) ∨ p5) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64818626513235213869460943782 : ((p2 ∨ (((((p5 ∧ p1) → ((p4 → ((((p1 ∧ p2) ∨ p2) → (p1 → p2)) → p2)) → p3)) → ((p2 → p4) ∨ True)) → p5) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54606947898905688017193806879 : (((p2 → (p5 ∨ ((p4 ∨ (False ∧ p1)) ∧ p2))) ∨ ((((p1 → p5) ∨ (((p5 ∨ p5) ∨ False) → (p5 ∨ (p2 ∧ False)))) ∨ True) ∨ p5)) ∨ p2) := by
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
theorem thm_5_vars_749635548566531066752237876230 : (((True ∧ (((((p1 ∨ (((p4 ∨ (p2 ∨ ((p3 → p5) ∧ p3))) ∧ p4) ∧ p5)) ∨ p2) ∨ (True ∧ (False ∨ (p3 ∨ p5)))) ∨ False) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788659014926734762976528896162 : (((p5 ∨ ((((p2 → (p4 ∧ (((p3 ∧ (p5 → p5)) → p3) ∧ ((p3 → (p1 → True)) ∨ p2)))) ∨ p3) ∧ (False ∨ (p1 ∧ True))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356451810055372843439699815877 : (p5 → ((p3 ∧ (p4 ∨ (((p2 ∨ p1) → (p4 ∧ p5)) ∨ (p3 ∧ True)))) ∨ ((p2 → (p1 ∧ (p4 ∧ ((p5 → (p2 → False)) ∨ p3)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685777248807093630347202755531 : (((((((False ∨ (((p2 ∨ p1) → (p3 → p5)) → ((p4 → p5) ∧ p2))) ∨ p3) → False) → p2) → ((True → False) ∨ (True ∨ (p5 ∧ False)))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_147855432341506683852402685691 : (((False → ((((p5 ∧ (p1 → p2)) ∧ (p4 ∨ (p2 ∨ ((p2 ∧ p5) ∧ False)))) ∧ (p5 → True)) ∧ p4)) → False) ∨ (True ∨ (p3 ∧ (p3 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111873881143960903903544960436 : ((((True → ((p1 ∨ (((p3 → (p4 ∧ p5)) → p1) ∧ p2)) ∨ (p2 ∨ (p3 → p4)))) ∨ ((p4 → p1) ∨ (p3 ∨ True))) ∨ p3) ∨ (p4 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_778113465012837138392952973592 : (((p1 ∨ ((p2 ∧ p3) ∨ ((p2 → (((p4 ∨ False) ∧ p5) ∨ p2)) → ((((False ∧ (p2 → (True ∨ False))) ∧ p2) ∨ True) ∨ (False ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787592763722516956437588274297 : (((p4 ∨ (p2 ∨ ((False → ((False ∧ p3) ∧ ((False ∨ ((False ∨ (p3 ∧ p4)) → p3)) → p3))) ∧ ((p2 → ((p1 ∧ p2) ∨ p4)) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349994563129303004641735927706 : (p4 → (((((((p5 ∨ True) ∨ p4) ∧ p5) ∧ (p2 → p4)) ∨ ((False ∨ (p1 ∧ p1)) ∨ (((p1 ∨ p2) ∧ False) → (p4 ∨ p5)))) ∨ p4) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644118649534034089178898954260 : ((((True ∨ (True ∧ ((((p4 ∧ (p3 ∨ False)) → p2) → p4) ∧ ((True ∧ (p5 ∨ p4)) → ((p3 ∨ True) ∧ (True ∧ (True → p4))))))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



