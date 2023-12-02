variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157356816335824324450863736281 : (((False → ((True ∨ (p3 → True)) ∧ (((True ∨ (((p3 → p3) → p1) ∨ True)) ∨ True) ∧ p5))) → False) ∨ (((p2 ∧ (p1 ∧ True)) ∨ False) → p1)) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205151396670991878131020522848 : (((False ∧ (False ∧ False)) ∧ (p5 ∧ p4)) ∨ ((True ∨ p2) ∨ ((True → ((p5 ∧ (True → True)) ∨ ((p4 ∨ (p3 → (False ∧ False))) → True))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112070442969474982122774264441 : ((((p2 → p3) ∧ ((p5 ∨ (((p2 → (p4 → (((p4 ∧ p2) → (p4 ∧ (p3 ∧ True))) ∨ p1))) ∨ p1) → p4)) ∧ p5)) ∨ p3) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84734103001785623232942158773 : (((((((False ∧ (p1 ∧ p4)) ∨ False) → True) → p2) ∧ ((p1 ∧ True) → p5)) ∧ ((p1 ∨ ((p2 ∨ ((p4 ∨ p4) → False)) → p3)) ∧ p1)) → p2) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : (((False ∧ (p1 ∧ p4)) ∨ False) → True) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h9
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h13 : (((False ∧ (p1 ∧ p4)) ∨ False) → True) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h15 := h4 h13
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51504095813552527844422021522 : ((((p2 ∨ (p2 ∧ p3)) ∨ ((((False ∧ (p4 → False)) ∧ (True ∨ p4)) ∧ (p5 → p2)) → p2)) → (p1 ∧ ((p2 ∧ (False → True)) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165685848992178233658847919040 : (((((p1 ∨ p3) → p3) → (p1 ∧ p3)) → (((p2 → ((True → p4) ∧ p1)) ∧ True) ∨ p4)) ∨ ((False → ((False ∧ (True ∧ p4)) ∧ p1)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300367747818920116883190706264 : (False ∨ (((((p1 → (p1 ∧ False)) ∨ True) → (p3 ∨ (((p1 ∨ p4) → (((p5 ∨ True) ∨ p4) ∧ False)) ∧ p1))) → p4) ∨ (False → (True ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184369718878386430279083262209 : (((p4 ∨ ((((p5 ∨ p4) ∧ (False ∨ p4)) ∨ p1) ∨ p3)) → False) ∨ ((True ∧ ((p2 ∧ ((((p1 ∨ True) → False) ∨ p1) → p1)) → p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4482707054616955901031408795 : (p2 → ((p3 ∧ p1) ∨ ((p5 → (((((p2 → p4) → p3) ∧ (((True ∧ p4) ∨ (p2 ∨ p1)) ∧ p1)) ∨ p4) ∨ (p1 ∧ p5))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248884429256373418486389798520 : ((p3 ∨ p5) ∨ (((((p2 ∧ p4) ∧ p1) ∨ (((False ∨ (p3 → p4)) ∧ False) → (p4 ∧ p2))) ∨ p4) ∨ ((False → False) → (p2 → (False → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185532383958141856204915253698 : ((p3 ∨ (((p3 ∧ p3) → p5) → (p1 ∨ (p2 ∧ (True ∧ True))))) ∨ ((p2 → (((True → ((p2 → p5) ∧ p5)) ∨ p2) → (p1 ∧ False))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314279451457177595941091803572 : (p3 ∨ ((p4 ∨ ((p4 → (p2 ∨ ((True ∧ True) → p3))) ∨ (((p2 ∧ p4) → (p4 ∨ (p1 → p1))) → (p3 ∨ p2)))) ∨ (False → (p2 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65972529440243040699104977327 : ((p4 ∨ (True → (p4 → (((p2 → p1) ∨ ((p2 ∧ p5) ∧ ((False → ((False ∧ (True → p1)) ∧ p3)) ∧ True))) ∧ ((p2 → p5) ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187798055957841345546594266149 : ((p3 → (p1 ∨ ((p1 ∧ (p5 → ((p5 ∧ p3) → p3))) → p1))) → (((p2 ∧ p3) ∧ (p1 ∧ (p1 ∨ False))) ∨ ((False ∧ p2) → (False → p2)))) := by
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
theorem thm_5_vars_251983956269056296229899928454 : ((p4 → False) ∨ ((p5 → (False ∧ ((p4 ∨ (p1 ∨ ((p4 ∨ (True ∨ True)) ∧ p3))) ∨ p2))) → ((p4 → (p3 ∨ (p1 ∧ False))) ∨ (p5 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57198457161328052483350286933 : ((((p4 ∨ p4) ∨ p1) ∨ (((p2 ∧ False) ∨ True) ∨ ((p5 ∨ ((p3 → (p4 → p2)) → (((p5 → (True → False)) ∨ p3) ∨ False))) ∧ p4))) ∨ p5) := by
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
theorem thm_5_vars_64986769356940284234761279557 : ((p2 ∨ (((False ∨ p4) ∧ False) ∧ (p2 ∧ ((p4 → p2) → (((False ∨ ((p3 → p1) → p4)) ∨ ((p1 ∨ True) ∨ False)) → (p5 ∨ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587180982133636810637835315737 : (((((p4 → (True ∧ (p3 ∨ (((p2 → p4) ∨ ((p4 ∧ (p4 ∧ p3)) ∨ (p4 → p2))) ∧ ((True ∨ (p2 → True)) ∧ p1))))) ∧ p3) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52994545827978990231690311975 : ((((p1 ∨ ((False ∨ ((True ∨ p2) ∨ p4)) ∨ False)) ∨ (p3 → False)) ∧ ((p1 ∧ (p1 ∧ False)) ∧ (True ∧ (p3 ∧ (p3 ∨ (False ∧ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191610119323681994696415350182 : ((p3 ∧ (((p4 → p4) ∧ (True → p3)) → (p1 ∨ p2))) ∨ (False → (((p5 ∧ (((False ∨ p4) ∨ (p5 → False)) ∨ (p1 ∧ p2))) ∨ p5) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230068328025347826026700765679 : (((p2 ∧ p2) ∧ p2) → (p4 ∨ (p4 ∨ ((p4 ∨ ((((p3 ∧ ((p2 ∧ (p2 → (p2 ∨ True))) ∧ p2)) → p4) ∧ (p4 ∧ p4)) ∧ p4)) ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_239593620821076144397730275399 : ((p3 ∨ True) ∧ ((p3 ∧ ((p3 → False) ∨ (((p2 ∨ (p4 → False)) ∧ p2) ∨ ((p5 → True) ∧ p2)))) → (p1 → (p5 ∨ ((True ∨ True) → p1))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h15 =>
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h19 =>
          -- One of the premise coincides with the conclusion.
          exact h2
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h25 =>
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177667592755355843056714478701 : ((((((p1 → ((p2 ∨ p2) ∧ p5)) → (True ∧ False)) ∧ p3) → p4) ∧ p1) ∨ (True ∧ ((p4 ∨ p1) ∨ (p1 ∨ (True → (p5 → (p5 ∧ p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41106168441942474963072395231 : ((((((True → p5) → p4) ∨ (((False ∨ (True → p5)) ∨ True) → (((p4 ∨ p4) ∧ False) ∨ (p1 ∨ True)))) ∧ ((p3 ∨ False) ∨ p4)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41016893221203445604525796859 : (((((p3 → (False ∨ (((True → (p3 ∧ ((p2 ∧ (False ∨ (p4 ∧ p2))) ∧ p4))) → (p3 → True)) ∨ p4))) ∨ p4) → (True → p1)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646739104616672325034608857634 : ((((p2 → (((p2 → (((True ∧ p2) ∧ p3) ∨ p2)) ∨ (p1 ∨ (((((p3 → p2) ∧ False) ∨ p1) ∨ (p5 ∨ p3)) ∨ p2))) → p1)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147356828776675574436952359925 : ((((((p3 ∨ p3) ∧ p5) → ((p1 ∧ p1) ∨ (True ∧ ((p1 ∨ p1) ∧ False)))) ∨ (p1 ∨ (True ∨ p5))) ∨ False) ∨ (p4 → ((p5 → p5) → p3))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150222577799299207301994206279 : ((p2 → (p4 ∧ (((p4 → p1) ∧ (p2 ∨ (p3 ∨ p1))) → (((p1 ∧ (True ∨ (p5 ∨ p5))) → p1) ∧ False)))) ∨ ((p4 ∧ p1) → (p3 ∨ p1))) := by
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
theorem thm_5_vars_161465244366953667080659901012 : ((p3 ∧ ((((p4 → p5) → (((p3 ∧ (p2 ∨ p2)) ∧ p1) ∨ p5)) → False) ∨ ((p5 ∨ True) ∨ p4))) → (p5 ∨ ((False ∧ p2) → (p4 ∧ p4)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
    -- Conjunctions on the left can always be decomposed.
    let h8 := h5.left
    let h9 := h5.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
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
        -- Implications on the right can always be decomposed.
        intro h14
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- False on the left can always be used.
        apply False.elim h15
        -- Conjunctions on the left can always be decomposed.
        let h17 := h14.left
        let h18 := h14.right
        -- False on the left can always be used.
        apply False.elim h17
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- False on the left can always be used.
      apply False.elim h21
      -- Conjunctions on the left can always be decomposed.
      let h23 := h20.left
      let h24 := h20.right
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209518705454961289401931954380 : ((p4 → ((p3 ∧ (True ∨ p5)) → p2)) → (((p1 ∧ (p1 → p2)) ∨ ((p1 ∨ ((p3 ∧ p5) → (((True ∧ p2) → p4) → p5))) ∨ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76972219476477481695757961767 : ((((False ∨ (p4 → (((p2 ∧ p2) → p4) ∨ p3))) → (p1 → ((p2 → (False → (((p3 ∨ p2) → p5) → p1))) → (p5 ∨ p1)))) → p2) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ (p4 → (((p2 ∧ p2) → p4) ∨ p3))) → (p1 → ((p2 → (False → (((p3 ∨ p2) → p5) → p1))) → (p5 ∨ p1)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49151221218049621086917588598 : ((((p2 → (p2 ∧ (p3 → (p1 ∨ (p4 ∧ p2))))) ∧ ((p3 ∧ (p4 ∧ True)) ∧ ((p5 ∧ True) ∨ (p2 → p3)))) ∨ (False ∧ (p3 ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114140879450787811604465318648 : ((((p1 ∧ ((((((False ∧ True) ∨ (p1 ∧ p2)) ∧ False) ∧ p2) ∨ (True ∨ p1)) → (p2 ∧ p5))) ∧ p1) → ((p5 ∨ p2) ∧ p2)) ∨ (True ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((((False ∧ True) ∨ (p1 ∧ p2)) ∧ False) ∧ p2) ∨ (True ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h13 : (((((False ∧ True) ∨ (p1 ∧ p2)) ∧ False) ∧ p2) ∨ (True ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h14 := h12 h13
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200992655275558100936499733421 : ((p3 ∨ ((p4 ∧ (p3 ∧ (p3 ∧ p3))) → p4)) → (p5 ∨ ((((p3 ∨ p1) ∨ p4) ∧ ((True → True) ∨ False)) ∨ (True ∧ (False → (p5 ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55468395555008452200990238950 : (((((p5 → p5) → False) ∧ (p2 → True)) → (((p4 ∨ (((p5 → (p5 → (False ∧ p3))) ∧ (p5 → p4)) ∨ (p3 ∨ True))) ∧ True) ∨ p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_314432161817912966413177681040 : (p3 ∨ (((p2 ∧ p5) → (p5 → (((p1 ∨ ((((p3 ∨ p4) ∨ p2) ∨ (p2 ∨ p4)) ∨ p2)) ∨ p3) → p1))) ∨ ((p4 ∧ (p5 ∨ p2)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258957757492889773242924942581 : ((True → p3) → (((p4 ∧ ((p3 ∧ p1) ∨ ((False → (((False ∧ p5) ∧ (False → False)) → (False → p4))) → p3))) ∨ (True ∨ p3)) ∨ (p2 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51712828920292016506643425861 : ((((False ∨ (p3 ∧ (False → (p5 ∧ (p5 ∧ p1))))) ∨ (p4 → ((True → p1) ∨ p3))) ∧ (((p5 ∨ (p3 → p2)) → False) ∧ (p2 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43153890434923681960433186832 : ((((((False → p5) ∧ (p2 ∨ p4)) ∧ ((False → ((p2 ∨ (p3 → (((p1 ∧ (p2 ∧ p3)) ∨ p3) ∧ p5))) → False)) ∨ p2)) ∧ p1) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147792452748335098761893022824 : (((True ∧ (p3 ∨ (p5 → (p1 → (((p4 ∧ p5) ∨ False) ∨ (((p3 ∨ (p2 → True)) → p5) ∧ p2)))))) → p4) ∨ (p3 ∨ (p5 → (p4 → True)))) := by
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
theorem thm_5_vars_81187194109253808821166615928 : (((p5 ∧ ((((p3 → True) → True) → p2) ∧ (p3 ∨ (p4 → (((p5 ∧ True) → (False ∧ (p1 → False))) ∧ False))))) ∧ ((p1 → p4) → p2)) → p2) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : ((p3 → True) → True) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h11 := h6 h9
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h13 : ((p3 → True) → True) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h15 := h6 h13
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234126159412399401438113038449 : ((True → (p3 ∨ False)) → ((p3 ∧ (((p4 → ((((p2 ∨ True) → p4) ∨ ((p3 ∧ (p5 → p4)) → p1)) ∧ p4)) ∨ p4) → p3)) ∨ (p5 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328896937738915668453950855446 : (True → ((p5 ∧ ((p4 ∧ ((p5 ∧ False) → p1)) ∧ p2)) ∨ (((p2 ∨ ((p2 ∨ p4) → p4)) → p3) ∨ (((p3 → True) ∨ (p2 ∨ p4)) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162332686048841938473267190559 : ((((p4 ∨ (p1 ∧ ((True → ((True → False) ∧ ((p3 → p4) → False))) ∧ p5))) ∧ p3) ∨ True) ∧ (False → ((((p4 → p2) ∨ p5) ∧ p3) ∧ p1))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338294292874430305597784268354 : (p1 → ((p4 → ((False ∧ p5) ∧ (p4 → p4))) → ((p1 → (((p5 → (p3 ∧ p3)) ∨ ((False ∧ False) → p5)) ∨ p3)) ∨ (True → (False ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628317976157181945193805602769 : ((((((True → p1) → ((p1 ∧ ((p3 → ((p3 → (p2 → ((p2 ∧ p1) ∧ p4))) → p5)) ∧ ((p1 → p4) → False))) ∨ p4)) ∧ p5) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741663953652162063027699883276 : ((((True → False) ∨ (((((p2 → p2) ∨ p5) ∨ (p1 ∨ (p3 ∨ p1))) ∧ ((p2 → p3) ∧ (False → p5))) ∧ (p5 ∨ (True → (p4 ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585480438062837797756435065886 : (((((((True → ((p1 ∧ p1) ∧ (False ∧ ((p3 ∧ (p2 ∨ ((True → ((False ∨ p4) → p1)) ∧ p4))) ∧ False)))) ∧ p5) ∨ p4) ∧ True) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54783605572807999183727851615 : (((p2 ∧ (p4 ∨ ((p2 ∨ (p2 ∨ False)) ∧ p5))) → ((((p1 → p5) → ((p1 → p4) ∨ (p4 ∧ (p2 → False)))) ∨ (True → True)) ∨ p3)) ∨ p5) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_904546373504449651695068982479 : (((((p4 ∧ (p4 → (True ∧ (True ∧ ((False → ((p5 ∧ p4) ∨ p2)) ∧ p2))))) ∧ ((True → p5) ∨ True)) ∨ (p2 ∧ (p1 ∨ (True ∨ p5)))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    cases h4
    case inl h7 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h8 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h9 := h6 h8
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h14 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h15 := h6 h14
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- We need to get the right conjuct of h17 based on <expert-advice>.
      let h18 := h17.right
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h25 =>
        -- One of the premise coincides with the conclusion.
        exact h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646677309330940199647793086384 : ((((p2 → (((((p5 ∨ p3) ∧ (((p2 ∨ True) ∨ False) → p3)) → ((False ∧ (p1 ∨ True)) → ((False ∨ True) → p2))) ∨ p5) ∧ False)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655862094969810910750321127319 : ((((((p1 → (True ∧ (True ∨ True))) ∧ ((((True → ((p2 → p1) ∧ p3)) ∨ p3) ∧ p3) → False)) → ((p1 ∨ p5) ∨ p3)) ∨ (p3 → True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_310331671808464110387601881339 : (p2 ∨ (((False → ((p3 ∨ p2) ∧ p3)) ∨ (p2 ∨ (p1 ∧ p5))) → ((p4 ∧ (((p3 ∧ (p3 ∨ False)) → p2) ∨ p5)) ∨ (p3 → (True ∨ False))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610478084533409972691425419225 : ((((((p5 ∧ ((p4 ∨ True) → ((((p2 ∨ p5) → p2) → (True ∨ (p3 ∧ (p3 → (p1 ∧ (p2 ∧ p2)))))) ∧ p1))) → p4) → p2) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_41330965302961823983608370052 : (((((True ∧ (((p2 → (p5 ∨ ((p3 ∨ p5) → p2))) ∨ (p4 → p3)) ∨ p3)) ∧ p2) ∨ ((p1 ∨ (False ∧ p4)) ∧ (p2 ∧ p3))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180057117813224978398325565410 : (((p4 ∨ (p2 ∧ (p5 ∨ (p4 → ((p3 ∧ (p5 ∧ p3)) ∨ True))))) ∨ True) → (((True → p4) ∨ True) ∨ (((p1 ∨ p3) ∨ p2) → (p1 → True)))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179860391185039462719734856643 : (((False → ((p4 → (True ∨ ((True ∧ False) ∨ p3))) → (p4 ∨ True))) ∧ p4) → ((p3 ∨ (((p3 ∨ ((p2 ∨ False) ∨ False)) ∨ p2) ∨ True)) ∨ True)) := by
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
theorem thm_5_vars_112624849411813213227644238332 : (((((((True ∨ (p5 → p4)) ∧ ((((True ∧ p3) ∨ p1) ∧ p3) ∧ (True ∨ p2))) → (p1 → p3)) ∧ p3) → (p5 ∨ True)) → p3) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7879234982049566686130638590 : ((((p4 ∧ ((((p5 ∨ True) ∧ False) → False) → ((((((True → ((True ∧ p5) → True)) → True) ∧ p3) ∧ p2) ∧ p5) ∧ p5))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173442533035651979696368029282 : ((((((p4 ∨ (p2 ∨ ((p4 → p3) → p2))) ∨ True) → (p5 → p1)) ∧ p4) ∧ p2) → (p1 → ((p2 → (False → True)) → ((p1 ∨ p4) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232061335431833154359831682172 : (((p4 ∨ True) → p5) → (True → (((p1 ∨ (p2 ∧ ((p2 ∧ p5) ∧ (((True ∨ p2) → p4) ∧ (True ∨ p3))))) ∨ (False → (False ∨ p3))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_955812531903823059773993661045 : (((((True ∧ p4) ∨ True) → (((p4 ∧ (p5 → (((p2 → (p2 ∧ p3)) ∧ p2) ∨ p2))) ∧ p5) ∧ (p2 → (p2 ∧ (p3 → (p5 → p2)))))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∧ p4) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50256281866609727139433335098 : ((((True ∨ (((((True ∧ (p1 ∨ True)) → (p4 → p5)) ∨ (p4 ∨ p2)) ∧ p1) ∨ (p4 → p1))) → p3) ∨ (((p1 ∨ p1) ∧ p2) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37286421669304521218240683787 : ((((p3 ∨ ((((((p4 ∨ p1) ∧ (p4 → False)) → False) ∧ (p4 ∨ True)) ∧ p4) → ((True → ((p5 → p1) ∨ True)) ∧ p1))) ∧ p3) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200519100909221650544466779207 : (((p1 ∨ p3) → (False ∨ (False ∧ (False ∨ p1)))) → ((((p1 ∨ ((True ∨ p3) → True)) ∨ p4) ∧ p3) → (p1 ∧ (((p1 ∨ p5) ∨ True) ∨ p3)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : (p1 ∨ p3) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h8
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- False on the left can always be used.
        apply False.elim h12
  case inr h14 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h15 : (p1 ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h16 := h1 h15
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- False on the left can always be used.
      apply False.elim h19
  -- Conjunctions on the left can always be decomposed.
  let h21 := h2.left
  let h22 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h21
  case inl h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h22
  case inr h26 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213357227279796659890664981570 : (((p4 ∧ (p4 ∧ p4)) ∧ p2) ∨ (((True → p2) → (((p5 ∨ ((False → False) → p2)) ∧ p2) → ((p3 ∨ p2) ∨ False))) ∨ (p1 ∨ (p4 → p2)))) := by
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
  cases h3
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617492447012118883063103535038 : (((((((p5 → False) ∨ (p1 → p5)) → False) ∧ (False ∨ ((p1 ∨ ((p1 ∨ p2) → p1)) ∧ (True ∧ (p3 ∨ ((False ∧ p2) → False)))))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136297377364185345766570759129 : (((False → ((p3 ∧ (p3 ∧ p3)) ∧ True)) → (((p2 → True) ∧ ((True ∨ p1) ∨ p1)) ∧ (False ∧ ((False ∨ p1) ∧ p3)))) ∨ ((p5 → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171624904262661482498249235813 : ((((p3 ∨ (p2 ∨ p4)) ∨ (p2 ∧ ((p5 ∨ False) → (p1 → (True → p3))))) ∨ True) ∨ (p4 ∧ (True → ((p1 ∨ (p2 → True)) ∨ (False ∨ p2))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112448465667530467782595276744 : (((((((False ∧ ((False ∨ p4) ∧ (p1 → (False ∨ ((p1 ∨ p5) ∨ p1))))) ∨ (p1 → False)) → p2) ∧ (p4 → p5)) ∨ p2) → p1) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204678573237965351306023782426 : (((False ∨ (p4 ∧ (p5 ∧ p5))) ∨ False) ∨ ((p1 ∨ (((p4 ∨ ((True ∨ ((p5 ∧ p4) ∨ p2)) ∧ True)) ∧ (True ∨ p2)) ∨ p3)) ∨ (p5 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41156908045676947959042106399 : ((((p3 ∧ ((((((True → (p3 ∨ True)) ∧ (p2 → (True ∧ p4))) → p4) → (p2 ∧ True)) ∧ False) ∨ p2)) ∨ (p2 → (True ∨ True))) ∨ p2) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54432352370797993544137825963 : (((((p3 → True) → (p5 → (p3 ∧ p1))) ∨ p3) ∨ (p3 ∨ ((p5 ∨ False) ∨ (p4 → ((p1 ∧ p5) → (p1 → (p4 ∧ (True ∧ p1)))))))) ∨ False) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740727213669501330439268036754 : ((((p2 ∨ p4) ∨ (((p1 ∧ p1) ∧ p3) ∨ (((p2 → (((((((False ∧ p2) ∨ p1) ∧ True) ∨ False) ∧ p4) → p4) → p4)) ∨ False) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315020198997926322347686635311 : (p3 ∨ ((((p2 ∨ p4) → p3) → (p2 → (p4 ∨ False))) ∨ (((False ∧ False) ∧ True) → (((p5 → (p4 ∧ (p5 → (p2 ∨ False)))) ∨ p1) ∧ p5)))) := by
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
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47043563103584641899773478549 : ((((((p5 ∨ True) → (p2 ∨ p4)) ∨ (p2 ∨ ((p2 → (p3 → (((p2 ∧ True) → False) ∧ False))) ∧ False))) ∧ (p1 ∨ True)) ∨ (True ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56380165679750083331776205464 : (((((p2 ∧ p2) ∨ p4) → False) → ((p1 → (p2 → True)) ∧ (((((p1 ∧ p2) → ((p1 ∧ (p1 → p2)) ∨ p1)) → p3) ∨ p4) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325880350884700463054274933320 : (p5 ∨ (p4 ∨ ((((p1 → (p4 ∨ (p2 → p2))) → p4) ∨ False) → ((((p5 ∨ (p5 ∧ p1)) ∨ (p3 → (p4 → (p5 → True)))) → False) → p3)))) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : ((p5 ∨ (p5 ∧ p1)) ∨ (p3 → (p4 → (p5 → True)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h4
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64416320598471006642678235811 : ((p1 ∨ ((p5 ∧ ((((p4 ∧ (p2 ∨ ((p3 → ((False ∧ ((p5 ∨ p3) ∧ p3)) → p2)) ∨ p5))) ∨ p5) ∧ p2) ∧ (p1 ∨ True))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138150044782955346205160154937 : ((p1 → ((p4 ∧ ((((p3 → ((True ∧ False) → (p4 → p4))) ∨ False) → ((p4 ∧ p2) ∧ p4)) ∧ (p3 → p4))) ∨ p3)) ∨ (False → (p3 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670145432945522080890931149856 : (((((((p3 → p3) ∨ (p2 → True)) ∧ p2) → ((((p5 ∨ p1) → p4) ∨ p4) ∨ ((p1 → p1) ∨ (p5 → p3)))) ∨ ((False ∨ p4) ∧ False)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660687448650847469619485617347 : ((((((p3 ∧ (((True ∧ (p4 → (p3 ∧ p3))) ∨ False) ∨ p4)) ∧ ((False ∧ p3) ∨ (p3 ∧ ((p5 ∧ False) → p4)))) → True) → (p2 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150554865575088678076118626159 : ((((False → (p3 ∨ (False ∧ True))) ∧ (p3 → (((p2 ∨ (p2 ∨ (p4 ∨ p5))) ∧ (False ∧ False)) ∧ p4))) ∧ p3) → (((p3 ∧ False) → False) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233663115175926120642534583358 : ((p2 ∨ (p4 ∨ p4)) → (p5 ∨ ((True ∧ ((True ∧ True) → True)) → ((p1 → p5) → ((((p2 → ((p2 ∨ p2) ∨ True)) ∨ p4) → p1) → p1))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : ((p2 → ((p2 ∨ p2) ∨ True)) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h8
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- Conjunctions on the left can always be decomposed.
      let h16 := h13.left
      let h17 := h13.right
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h18 : ((p2 → ((p2 ∨ p2) ∨ True)) ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h19 := h15 h18
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- Implications on the right can always be decomposed.
      intro h22
      -- Implications on the right can always be decomposed.
      intro h23
      -- Conjunctions on the left can always be decomposed.
      let h24 := h21.left
      let h25 := h21.right
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h26 : ((p2 → ((p2 ∨ p2) ∨ True)) ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h20
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h27 := h23 h26
      -- One of the premise coincides with the conclusion.
      exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747203102141315464934968498911 : ((((p5 ∨ p1) → ((((((p4 ∧ p3) → (p2 ∨ ((p1 → p3) → p5))) ∧ p5) ∨ (p1 ∨ p3)) ∨ ((p4 ∧ (False ∨ p3)) ∧ True)) ∨ False)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49956021840668234231169793452 : (((((p3 ∨ (p1 ∨ (p3 ∧ ((p2 → p3) → ((p5 → p5) → p3))))) ∧ (p2 → p5)) → (p2 ∨ False)) ∧ (False → ((p1 ∧ p4) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52147347856961079787813389060 : ((((p3 ∧ ((((p3 ∧ p4) ∨ p1) ∧ ((p1 ∨ p5) ∧ False)) ∧ p3)) → (True → p1)) → ((p5 ∧ (p5 ∨ p5)) → ((p1 → p3) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635969731215208078280030179055 : ((((((p4 ∧ ((p3 → (p4 ∧ (p1 → ((p4 ∧ (p2 → p4)) ∨ False)))) → p4)) → p3) ∧ ((((p5 ∧ p5) → p3) ∧ False) ∨ p5)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706965139708508035722879965887 : ((((((p2 → (p1 ∨ p2)) → (p1 → p2)) ∨ p4) ∨ (((p3 ∧ p1) ∧ (p1 → p1)) ∨ ((p3 → ((p4 ∧ True) ∨ (False → p3))) ∨ True))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_797955953477261702669227616368 : (((p1 → (((((p3 ∨ p2) → p2) ∧ ((p3 ∧ p5) ∨ True)) ∨ (p5 ∧ ((p4 ∧ ((False ∧ p4) → p5)) ∧ (p1 ∨ p5)))) → (p3 → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46158148794729027871941981421 : ((((((p1 → ((True ∨ (p1 ∧ p3)) ∧ (((p1 ∨ p1) ∨ p2) ∧ (p5 ∨ p3)))) ∨ True) → (True ∧ (p1 ∧ p2))) → p4) ∧ (p5 → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40174782849599282895936589090 : ((((((True ∧ (True → (p2 ∨ False))) ∨ p3) → (False ∧ (((p1 ∨ True) ∨ (p4 ∧ p3)) ∨ (True ∨ ((True ∨ False) → p3))))) ∧ p3) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624651506557705882785213450592 : ((((p4 ∨ ((p4 ∧ p3) ∨ ((((False ∨ (p2 → True)) → p1) ∨ True) → ((False ∧ p3) ∧ ((True → (p2 → True)) ∨ (p1 ∨ p1)))))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_148080310442603963326374193929 : (((((p1 ∧ ((p5 ∧ (((True ∨ (False ∧ p5)) ∧ p1) → (p2 → False))) ∨ p1)) → p3) ∨ p1) → (p4 ∨ False)) ∨ (False → (True ∨ (True ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54916884703530565408585515315 : ((((((p2 ∧ p5) ∨ p3) → False) → p5) ∧ (((p1 → (p2 ∧ False)) ∧ (p2 ∨ ((p2 ∨ (False ∨ True)) → False))) ∧ ((p3 ∧ False) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321254590610673422918226700595 : (p4 ∨ (p4 ∨ ((p2 → ((p1 ∧ p2) ∨ (((True ∧ (p5 ∨ p5)) → p3) → p1))) ∨ ((p4 ∧ False) → (p3 → (p5 → ((p5 ∧ p2) ∨ p3))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352373638863382225334279721701 : (p4 → (((p4 ∧ p2) ∧ p3) ∨ (p1 ∨ (p4 → (p5 ∨ (((((p1 ∧ (p4 ∨ p5)) → (p4 ∨ (p1 ∧ False))) ∨ p5) → (p5 ∨ True)) ∧ True)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247771290210010207435619965504 : ((p1 ∨ p1) ∨ ((((p1 ∧ (((p5 → p4) ∨ p1) ∧ (False ∨ (p1 ∧ ((((True ∨ True) ∨ p5) ∧ (p2 ∨ p5)) ∧ True))))) ∨ p4) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150777912157630448691658780674 : (((((((p3 ∧ p5) ∧ (p4 → p3)) ∨ p4) ∨ ((p3 ∨ p2) → (p2 ∧ ((p4 ∧ p2) ∨ True)))) → False) ∨ p2) → (((p3 → p3) → False) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (p3 → p3) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h4
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (p3 → p3) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h8
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43413222617362823332178844374 : ((((((p5 ∧ p1) → ((((p4 ∨ p1) ∧ p4) ∧ p1) → p3)) → (p5 ∧ (p2 → (p3 ∧ (((p1 ∧ True) → True) ∧ p5))))) ∨ p2) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



