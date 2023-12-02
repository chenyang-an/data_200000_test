variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232355121053734370782270315051 : (((p4 → p3) → False) → (((p4 → False) ∨ p3) → ((((p3 → True) ∧ p5) → (p1 → (((True → p1) ∨ (p5 ∨ p2)) ∧ (p2 ∨ p4)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
theorem thm_5_vars_225596731213095641741650632679 : (((False → p5) ∧ p1) ∨ (((((p4 ∧ (p3 → p3)) ∨ p3) ∨ (((p3 ∨ True) → (True ∧ False)) → (p2 ∧ True))) ∨ False) ∨ ((False ∧ p5) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
theorem thm_5_vars_695190061342982266925356753680 : (((((p4 ∧ ((p5 ∨ (p3 ∧ False)) → ((False → p4) → (p4 ∧ p1)))) ∨ False) → (p2 → ((((True → p4) → (p1 ∧ True)) ∨ p4) ∨ p2))) ∨ p3) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135952085436895412538105110777 : (((((False → p2) ∧ False) ∨ ((p5 ∨ (p3 ∧ False)) ∨ True)) ∧ ((((p3 ∨ p5) → p3) ∨ p3) ∨ ((p4 → p4) → True))) ∨ ((p1 → p3) ∨ p1)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314120529130729559926932489485 : (p3 ∨ (((p5 ∨ p1) → ((False ∨ ((((p3 → p4) → True) → (p4 ∧ True)) ∧ (p3 ∨ p5))) ∧ (((p3 ∨ p2) ∧ p2) ∧ p1))) → (p5 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p5 ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303983747706969776968611617983 : (p1 ∨ (((p2 ∨ p4) ∧ (((p4 ∨ p5) ∧ ((False → p1) ∧ ((p2 ∧ ((p1 ∧ (p3 ∧ (p5 → p2))) ∨ p5)) → (True → True)))) ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673706064109255696857181605398 : (((((p5 ∧ p4) ∧ ((p2 ∨ p4) ∨ (p3 → ((((p5 ∧ p2) ∧ (p4 ∧ (p3 ∧ p1))) → p3) ∧ (p5 ∧ p5))))) → ((p3 ∨ p2) ∨ p5)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h3
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55673473596326397031166176097 : ((((p5 → (p2 ∨ p4)) ∧ p3) ∧ (((p5 ∨ p4) ∨ p2) ∨ ((((p3 ∨ (False → p3)) → p1) → ((p5 → p3) → True)) → (True → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120117572408347898953613682047 : (((((True ∧ False) ∨ p2) ∧ ((((p2 → ((p2 ∨ (False → p3)) → p3)) → ((p3 → (p5 ∧ False)) → p3)) ∨ p3) ∨ p3)) ∧ p1) → (p3 → p3)) := by
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
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117954223655190578787826498776 : ((p5 ∧ (p3 ∨ (((((p3 ∧ (p4 ∧ False)) ∧ (p3 ∧ (p1 ∨ ((p3 ∧ False) → True)))) ∨ p2) ∧ ((p5 → p1) ∧ p2)) ∧ p4))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50456100700673493531374164197 : (((p4 ∨ ((True → ((False ∨ (False ∧ (((p1 ∨ False) ∨ p2) ∨ p4))) ∨ (True → (p3 → True)))) ∧ p2)) ∨ (((True → p3) → True) → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142969981716274938277028894285 : ((True → (((p5 → (p1 ∧ True)) ∧ (p3 ∨ (p1 ∨ (p2 ∧ ((((p5 → p5) → True) ∧ p4) ∧ (p2 → p5)))))) ∧ p4)) → (p4 ∨ (True ∧ p3))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136645268367994745486909409151 : ((((p3 ∨ False) → p5) → (((p2 ∨ ((p2 → p1) ∨ p5)) → ((p2 → (p4 → p4)) → False)) ∧ ((p5 ∨ p3) ∨ True))) ∨ (p5 → (p4 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46247344342478315419955351429 : ((((p2 → (p4 → (p1 ∨ ((p4 ∧ ((p4 ∧ p1) ∧ (p4 ∨ ((True → False) ∨ p3)))) ∧ (True ∨ True))))) ∨ (True ∨ p3)) ∧ (p5 ∨ True)) ∨ p5) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326836276760923323718713868990 : (True → ((((((p3 ∧ ((p1 ∧ p2) → (p3 → False))) ∨ ((True ∧ p4) → (p4 ∧ p2))) → False) → (p4 ∨ (p5 ∧ (True → p1)))) ∧ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133583425488553147487428942621 : (((((p4 → p1) ∨ (p1 → ((((p5 ∧ p4) ∨ p3) ∧ False) ∧ (p2 → (True ∧ ((p4 ∧ False) ∨ p3)))))) ∨ p2) ∧ p4) ∨ ((False ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137062346047003685501764668020 : (((p3 → True) → ((p1 → (((p2 → ((p4 → p4) ∨ p1)) ∧ (p5 ∨ (p4 ∨ (True ∨ p4)))) ∧ (p4 ∧ p1))) ∨ p3)) ∨ ((p1 → True) ∧ True)) := by
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
theorem thm_5_vars_658707419204565732538713572095 : ((((p4 ∨ ((p2 ∧ p1) → (((p3 ∧ (p4 ∧ False)) ∨ p3) ∨ ((True ∧ p4) ∨ (False → (((False ∨ p1) → True) ∨ p4)))))) ∨ (p5 ∧ False)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139861739644220874813115184454 : (((((True → ((False ∧ (p3 ∧ p2)) ∨ (((p1 → (p2 ∧ True)) → p1) ∨ (p2 ∨ False)))) → p5) ∧ p5) ∧ (p4 → p2)) → (p2 → (True → p5))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262621539648738081777040195294 : (True ∧ (((((p1 ∨ p3) ∨ (True → (False ∧ (p3 ∧ False)))) → (((True → True) → ((p5 ∧ (p5 ∨ False)) ∨ (p1 ∨ True))) ∧ True)) → p5) → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ p3) ∨ (True → (False ∧ (p3 ∧ False)))) → (((True → True) → ((p5 ∧ (p5 ∨ False)) ∨ (p1 ∨ True))) ∧ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350002033912096527506695250869 : (p4 → ((((True → p5) → ((False ∨ ((p1 → True) → (False ∨ ((p2 → ((((p5 ∨ True) ∧ p3) ∨ False) ∧ p2)) → p5)))) ∨ p1)) ∨ False) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738061707052964032842154926700 : ((((False ∧ True) ∨ (p4 ∨ (p3 → (p5 ∨ (((p1 ∨ p4) → True) ∧ (((False → p4) → ((p1 ∨ (p2 ∨ False)) ∧ True)) ∨ (p4 ∧ p3))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306379618532278371583494246878 : (p1 ∨ ((p4 → True) ∧ ((((p1 ∨ (p5 → p5)) → p3) ∨ (p1 ∨ ((p4 → ((p1 ∧ (False ∧ p1)) ∧ p4)) ∧ (p1 ∧ p2)))) ∨ (p4 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39364580806660231397683895963 : (((p3 ∧ ((p5 → (False ∧ ((((True ∨ p3) ∧ True) ∨ (p3 → ((p4 → (p3 → False)) ∧ (p2 ∨ p4)))) ∧ False))) ∧ (True → p5))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_892599277828737244511500011103 : (((((((((((False → p4) ∧ True) ∧ (p2 ∧ p5)) → True) ∨ (p4 ∧ p5)) → (True → p2)) → p3) ∧ (p1 → p5)) ∧ (p2 ∧ (p1 ∨ p4))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h7
  case inl h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : ((((((False → p4) ∧ True) ∧ (p2 ∧ p5)) → True) ∨ (p4 ∧ p5)) → (True → p2)) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- One of the premise coincides with the conclusion.
        exact h6
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h16 := h4 h9
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h17 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h18 : ((((((False → p4) ∧ True) ∧ (p2 ∧ p5)) → True) ∨ (p4 ∧ p5)) → (True → p2)) := by
      -- Implications on the right can always be decomposed.
      intro h19
      -- Implications on the right can always be decomposed.
      intro h20
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h21 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- One of the premise coincides with the conclusion.
        exact h6
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h25 := h4 h18
    -- One of the premise coincides with the conclusion.
    exact h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47364051377860262026037825624 : ((((p4 ∨ False) ∨ (p3 ∧ (True ∧ (p1 → (p5 ∨ ((p3 → p1) ∧ (((p2 ∨ ((p2 ∨ p5) → p4)) ∨ False) ∧ p4))))))) ∨ (False → p4)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112707523964713807612660628479 : (((((p1 ∨ True) → (p1 ∨ (((p3 → (p4 → (p2 → True))) ∨ True) ∧ (True ∨ p1)))) → (True → ((p2 ∨ True) → p2))) → p1) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147264691013738225580729636327 : (((((p4 ∨ (((p4 ∧ ((True ∧ (False → p5)) → p3)) ∧ (p2 ∧ (p3 ∧ p2))) ∨ False)) ∨ p5) ∨ p5) ∨ p4) ∨ (False ∨ (p1 ∨ (False → p4)))) := by
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
theorem thm_5_vars_788464691624552532352580020560 : (((p5 ∨ (((p4 ∨ p3) ∧ ((False → (p5 ∨ ((p4 → False) ∨ ((p2 ∧ False) → ((((p3 ∨ False) ∨ p1) ∧ p5) ∨ p3))))) → p2)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783465425929851706857828894420 : (((p3 ∨ (((p2 ∧ (p5 → (((p5 → True) ∧ True) → ((p1 ∨ p5) → p5)))) → p1) → (p3 ∨ ((p5 → ((p1 ∨ p2) ∧ p1)) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208980116119501538323021998359 : ((True ∨ (p3 ∨ (True ∧ (p1 → False)))) → ((True ∧ ((True ∧ (True ∨ (True → p4))) → ((p2 ∧ p2) ∧ (p5 ∧ False)))) → ((p5 ∨ p4) ∨ p3))) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (True ∧ (True ∨ (True → p4))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h15 : (True ∧ (True ∨ (True → p4))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h16 := h4 h15
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- We need to get the right conjuct of h17 based on <expert-advice>.
      let h18 := h17.right
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54580040470848700198650816347 : (((p2 ∨ (((True ∧ p2) ∧ p2) ∨ (p1 ∨ p2))) ∨ ((p1 → ((p2 → False) ∨ p2)) ∨ ((p5 → (((p2 ∧ True) ∧ p4) ∧ p4)) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322354751921638474662673006921 : (p5 ∨ ((((True ∧ (p1 → (((p5 ∧ ((True ∧ (p4 ∨ p4)) ∨ p2)) ∨ (True ∧ (p3 ∨ False))) ∨ p4))) ∨ True) ∨ ((p3 → False) ∧ p5)) ∨ p4)) := by
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
theorem thm_5_vars_137237349713207116067833804505 : ((p1 ∧ (((p1 → ((p3 ∧ True) → (((True → (False ∧ False)) ∧ (False ∧ False)) ∨ p4))) ∨ p4) ∧ (p1 → (p5 ∧ p4)))) ∨ ((p4 → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674265753640741559496040159073 : ((((True ∨ ((p4 ∨ (p1 ∧ (p3 ∨ (p4 ∧ (p2 ∨ (False ∨ True)))))) → (p1 ∨ ((False → (p3 ∧ p3)) ∨ p1)))) → (p2 ∧ (p4 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113320709803465969143796302550 : (((((p3 ∧ False) → p4) → ((False ∧ (False ∧ (p2 ∧ p4))) ∨ (((p3 ∨ p5) → ((p1 → p5) ∨ True)) → p5))) ∧ (p2 → p3)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352713917996442109413772633465 : (p4 → ((p1 → p2) ∨ ((p1 ∨ (False ∨ (p3 ∨ p4))) ∧ (False ∨ ((p1 ∨ (p4 → (True ∨ ((True ∧ p3) → p4)))) ∨ ((False → p4) → p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52344181154354757377833981032 : (((((p2 ∨ p3) ∧ (True ∧ ((p2 ∧ p2) ∨ ((p5 ∨ p1) ∨ p4)))) → False) ∧ ((((p1 → p2) ∨ (p5 → p3)) → False) ∨ (True ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219042374190669058140581542121 : ((p5 ∧ ((p1 ∧ False) → p4)) → ((False → (p2 → False)) ∧ ((((p2 ∨ p2) ∨ p4) ∨ ((p5 ∨ p5) → ((True → p1) ∧ False))) ∨ (True ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621307945163144664175830628507 : ((((True ∧ (((p3 ∧ (p1 ∨ True)) ∧ (p2 ∧ False)) ∧ ((False → True) ∧ (((p5 ∧ (p5 ∧ True)) ∧ ((False ∨ p1) ∧ p5)) ∨ False)))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_55139444632222191631732102122 : ((((((False → p1) ∨ p3) ∧ False) ∨ p2) ∨ (((False → (p5 ∨ (True ∨ False))) → ((False ∨ p3) ∨ False)) ∨ (((p4 → p4) → p2) → p2))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165939214832065667053616985122 : (((False ∨ False) ∧ ((p3 ∧ ((True ∨ (((p1 → p5) → p4) → (False → p1))) ∧ True)) → p5)) ∨ ((p3 ∨ p1) ∨ (((True ∧ True) → False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116238875007624965718567728840 : ((((True ∨ p3) → p2) ∨ (((True → (((p4 ∨ (p3 → False)) ∧ p4) ∧ p5)) → ((p3 ∨ p1) ∨ p2)) → ((p3 → p5) ∧ p4))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_931335270345214053726644550327 : ((((True ∨ (((p3 ∨ (True ∨ p3)) ∧ p1) ∧ (True ∧ True))) → ((p5 ∨ ((p5 → p2) → (((p1 ∨ p4) ∨ p5) → p2))) ∧ (p5 ∨ False))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (((p3 ∨ (True ∨ p3)) ∧ p1) ∧ (True ∧ True))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315137017124250342756709119945 : (p3 ∨ ((p4 ∨ ((False ∧ (p4 ∧ p4)) ∧ False)) ∨ ((False → (((p5 ∧ p1) → (p2 ∧ ((p5 ∧ (False ∨ False)) → False))) ∨ p2)) ∨ (p1 ∨ p1)))) := by
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
theorem thm_5_vars_750547540232681663061787153019 : (((True ∧ (((((p3 → p4) ∨ ((p4 → p4) ∧ (p1 ∨ ((p2 ∨ p1) → p4)))) → (p1 ∨ p5)) ∨ False) ∨ (((p3 ∨ p3) ∨ p2) → True))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601446050575353657866589501167 : ((((p3 ∧ (((((p1 ∨ p2) → p2) ∧ True) → ((p5 ∨ ((p2 ∧ (p3 ∧ p1)) ∨ (((False → p1) → p3) ∨ True))) ∨ p1)) ∧ p4)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191665595705138289993208728520 : ((p5 ∧ (((((p5 → p4) → True) ∨ True) → False) ∨ True)) ∨ (((p4 ∧ (p2 ∧ True)) ∧ (p3 → ((True ∧ True) → p5))) → ((p4 → False) → False))) := by
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
  let h7 := h6.left
  let h8 := h6.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h9 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h9
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184738256491942511704523920612 : (((((p5 → p4) ∧ p2) ∨ p4) ∧ (((p3 ∧ p2) ∨ p5) ∧ p3)) ∨ (True ∨ (((p3 ∨ ((True ∨ (p2 → p4)) ∨ (p2 ∨ p3))) ∨ p4) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308504139517856363125614439311 : (p2 ∨ (((((p5 → True) ∧ p4) ∨ (((((p2 ∧ p1) → (p5 ∨ p3)) ∧ False) ∧ p5) ∧ (False → p4))) ∨ ((False ∧ (p3 ∧ True)) → True)) ∨ False)) := by
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
theorem thm_5_vars_115746194450225144053493596211 : ((((p2 ∧ p4) → (p3 ∨ (p5 ∨ p5))) → (True ∧ (((((p3 ∧ False) ∧ False) ∨ ((p3 → (p2 ∧ p3)) ∧ p3)) ∨ True) ∧ p2))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223869001589705495259043481653 : ((p3 ∨ (True → True)) ∧ ((p3 ∨ ((p4 ∨ False) → p1)) → (False ∨ (p1 → (((p5 ∨ (False → (p1 ∨ (p1 ∨ p3)))) ∨ p2) ∨ (p2 ∧ True)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111691501243491542065582355888 : (((((((((True ∧ ((p1 → (p3 ∨ p3)) → ((True → p1) ∧ p1))) ∨ p4) ∨ p4) ∨ (False ∧ p1)) ∧ p2) → p1) → p5) ∨ True) ∨ (p5 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134053795894043495205315900672 : ((((p2 ∨ ((p1 ∧ ((p3 ∧ (False ∨ (p2 ∨ p3))) ∧ ((p3 ∨ p5) ∨ p4))) → ((p5 → p5) ∧ p5))) ∨ p1) ∨ p4) ∨ (True → (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678566403430623469161942042480 : ((((((p1 ∧ p4) → True) → ((True → (True → p1)) ∧ (p5 ∧ ((p5 ∧ p4) ∨ ((p1 ∨ p2) ∨ False))))) ∨ ((p1 → p5) ∨ (True ∨ p1))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_187239551469988868672783885931 : ((True ∧ ((p3 → (p2 ∧ ((p2 ∧ p5) → (True ∨ False)))) ∨ p2)) → (p4 ∨ ((True → (((p5 ∨ p3) → (p5 ∨ (p2 → p4))) → False)) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246633369533293311916625908965 : ((p5 ∧ p3) ∨ (((((p1 ∧ True) ∨ p4) ∨ (p4 ∨ (((p1 → False) ∨ p1) ∧ (((p5 ∧ False) ∨ p1) → p2)))) → p4) ∨ (True ∨ (p2 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382036649819850774340573107651 : ((((((p5 ∨ ((((p4 ∨ False) ∧ p5) ∧ p1) ∨ ((p5 → False) ∧ ((True → False) ∨ (((p4 ∨ p2) ∧ p4) ∨ True))))) → p4) ∨ p3) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_166518205849920716640862995289 : ((p4 ∨ ((p4 ∨ ((p4 ∧ p3) ∧ (p2 ∨ (p5 → p5)))) ∨ ((p1 ∨ False) → (p2 ∧ p3)))) ∨ ((p3 ∧ ((p4 → p4) ∨ True)) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187107422343007205284517642727 : (((p1 ∧ p2) ∨ ((p5 ∨ (p1 ∨ (p3 ∧ (p1 ∧ p5)))) ∧ p1)) → (((p5 ∧ (p4 ∨ (p3 → (p3 ∨ p2)))) ∧ p2) ∨ (p3 ∨ (p1 ∧ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h7
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117041644205691767897752497925 : (((p3 ∨ p4) → (((True ∧ ((((p1 ∨ p4) ∧ p3) → p4) ∧ (False ∧ True))) ∨ (False ∧ p5)) ∨ ((True ∨ p3) ∨ (p3 ∨ p5)))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312375643678683165473327969401 : (p2 ∨ (p3 → (((((p2 ∨ p1) ∨ False) → (p3 ∨ p2)) → p1) → ((p5 ∨ (p3 ∧ ((p2 → (((p4 → False) ∨ False) → True)) → p5))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41514089668575949644490202435 : (((((((True ∨ (p5 ∨ (p5 ∧ p5))) → p1) ∧ p2) → p3) ∧ ((((p3 ∧ (False ∧ p5)) ∨ (p1 ∨ p4)) → (True → p3)) ∧ p5)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42494367243290601715139800695 : (((False ∨ ((((p2 → ((False ∨ True) ∧ p1)) → (((p4 ∧ True) ∨ (((p2 ∨ p3) ∧ p3) → True)) ∧ p4)) → (p1 ∨ p5)) → p3)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207769081728332429760973151604 : (((p3 ∨ ((p1 ∨ p1) ∨ True)) → False) → (((True ∧ (True ∧ ((p4 → p5) ∧ p1))) ∨ (True → True)) → ((False ∧ p5) ∧ (p3 ∧ (p4 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : (p3 ∨ ((p1 ∨ p1) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h13 : (p3 ∨ ((p1 ∨ p1) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h14 := h1 h13
    -- False on the left can always be used.
    apply False.elim h14
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h22 : (p3 ∨ ((p1 ∨ p1) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h23 := h1 h22
    -- False on the left can always be used.
    apply False.elim h23
  case inr h24 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h25 : (p3 ∨ ((p1 ∨ p1) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h26 := h1 h25
    -- False on the left can always be used.
    apply False.elim h26
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h27.left
    let h29 := h27.right
    -- Conjunctions on the left can always be decomposed.
    let h30 := h29.left
    let h31 := h29.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h31.left
    let h33 := h31.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h34 : (p3 ∨ ((p1 ∨ p1) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h35 := h1 h34
    -- False on the left can always be used.
    apply False.elim h35
  case inr h36 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h37 : (p3 ∨ ((p1 ∨ p1) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h38 := h1 h37
    -- False on the left can always be used.
    apply False.elim h38
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h39 =>
    -- Conjunctions on the left can always be decomposed.
    let h40 := h39.left
    let h41 := h39.right
    -- Conjunctions on the left can always be decomposed.
    let h42 := h41.left
    let h43 := h41.right
    -- Conjunctions on the left can always be decomposed.
    let h44 := h43.left
    let h45 := h43.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h46 : (p3 ∨ ((p1 ∨ p1) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h47 := h1 h46
    -- False on the left can always be used.
    apply False.elim h47
  case inr h48 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h49 : (p3 ∨ ((p1 ∨ p1) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h50 := h1 h49
    -- False on the left can always be used.
    apply False.elim h50



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47069100892852127727705252417 : ((((False ∧ ((p4 ∧ p3) ∨ (((p2 ∨ ((p5 → (p3 → True)) ∨ p3)) → (p3 → p2)) ∨ (p4 ∨ p4)))) ∨ (p5 ∨ p2)) ∨ (p5 ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148991108899674040046628019354 : (((p3 ∨ (p2 → p2)) ∧ ((p3 ∧ (p2 ∨ (True → ((p5 ∨ (p2 → (p3 → p5))) ∧ p4)))) ∨ (True ∧ True))) ∨ (((p4 → p1) ∨ True) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137965317353390835142290124295 : ((p5 ∨ ((p1 ∧ (((p3 → ((p1 ∧ p4) ∧ (p2 ∨ (True ∧ p1)))) ∨ (p3 ∨ True)) ∧ p3)) ∧ (False ∧ (False → False)))) ∨ (p4 ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642205664167521179426873571294 : ((((True ∧ (p3 ∧ (True ∨ (((p2 ∨ p4) ∧ (p1 ∧ (((((False ∨ False) → p4) → p5) ∧ p4) → ((p1 → False) ∧ p1)))) → p2)))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358107376193643999375615802424 : (p5 → (p2 ∨ ((p1 ∨ (p1 ∨ (False ∨ (((p4 → p4) ∨ (p3 → (p2 → p3))) → (p4 ∨ (p3 ∨ (p3 ∨ (True → p5)))))))) ∨ (False → False)))) := by
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
theorem thm_5_vars_65466151157279857851351984867 : ((p3 ∨ (True ∧ ((False ∧ ((p3 ∨ p2) ∧ ((True ∨ p1) ∧ p2))) ∨ (((p4 ∧ False) ∨ False) → (False ∧ ((p1 ∨ (p3 ∨ p2)) ∨ p1)))))) ∨ p3) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187750143714695508914468607399 : ((p2 → (((((False → (p2 ∧ p1)) → p5) ∨ True) ∨ p5) → False)) → ((p5 ∧ ((p4 ∧ p1) ∧ (True ∨ p2))) → ((p4 ∧ (True ∨ False)) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h13.left
  let h16 := h13.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h17 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h18 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h19 := h2.left
  let h20 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h20.left
  let h22 := h20.right
  -- Conjunctions on the left can always be decomposed.
  let h23 := h21.left
  let h24 := h21.right
  -- Disjunctions on the left can always be decomposed.
  cases h22
  case inl h25 =>
    -- One of the premise coincides with the conclusion.
    exact h19
  case inr h26 =>
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354663569504547954467276877746 : (p5 → ((((p3 → False) ∨ ((p2 ∧ ((p4 → p3) ∧ (False → (p5 ∨ p5)))) ∨ ((True ∨ ((p3 ∧ (p2 → True)) → True)) ∨ p2))) → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177873240778390627322731213333 : (((((p2 ∨ (p1 → (p4 → (p2 ∨ (p1 ∧ p2))))) ∧ p2) → p4) ∨ p3) ∨ (((((False → p1) → False) ∨ ((p2 → p2) ∧ False)) ∧ False) → p4)) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299464399138794493150804961186 : (False ∨ ((p5 ∨ ((p1 → (False → ((False ∨ p4) ∧ True))) → (((p3 ∨ ((p2 → (p2 → p2)) ∧ (p4 → p5))) ∨ (True ∨ p3)) ∧ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800436252214697599622205687099 : (((p2 → ((p5 ∨ (True → ((((((p3 → p4) → p1) ∨ (p4 ∧ True)) ∧ ((False ∨ True) ∨ (p3 ∧ p4))) → p5) → (p4 → p3)))) ∨ p2)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791863617314318659414743397798 : (((True → (((p3 → p4) ∨ (((((p1 ∧ (p1 ∨ False)) → True) ∨ True) → True) → (p2 ∧ (True ∧ ((p3 ∨ p4) ∨ p5))))) ∧ (p1 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249288417977922921050733195790 : ((p4 ∨ p5) ∨ (((((p2 → ((True ∧ (p3 ∨ p2)) ∨ ((False → True) ∧ (p2 ∨ p3)))) ∨ ((True → (p5 ∧ p2)) ∨ False)) ∧ p2) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65257635189092039240542864057 : ((p3 ∨ ((((p3 ∧ (p3 → p2)) → True) ∨ (((((p2 ∨ ((True → p2) → (True → True))) ∧ p2) → p5) ∧ True) ∧ (p4 ∨ p5))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114511475743566607536254201670 : ((((False ∨ p1) ∨ (p5 → ((False → (((True ∨ ((p4 ∧ p2) → p1)) ∧ True) ∧ False)) ∨ p3))) → ((p3 ∨ (p1 → True)) ∧ p3)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205180253020088708601733843967 : (((p2 ∨ (p5 ∧ p4)) ∧ (p3 ∧ p1)) ∨ ((((((p5 ∧ False) ∧ True) ∨ p2) → True) ∨ False) ∨ ((p2 ∨ (True ∧ (True ∨ True))) ∨ (False ∨ p1)))) := by
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
theorem thm_5_vars_113636619431743591171258515334 : (((p5 → ((p4 → ((p4 ∧ ((p4 ∧ ((False ∨ True) ∨ p3)) → p5)) ∧ (p2 ∨ p1))) ∧ (True → (True → p2)))) ∨ (p5 ∧ p5)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205499011957926246196437888348 : (((p2 ∧ p4) ∧ (p5 ∨ (p1 ∧ p2))) ∨ (p2 ∨ (p3 → (((True ∧ False) ∨ (p4 → p4)) ∨ ((p2 ∧ ((p1 → p3) ∨ p3)) ∨ (p4 ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64766560117722817072881855560 : ((p2 ∨ ((p5 ∨ ((True ∧ (False → False)) → ((p1 → p3) → (((True ∨ p2) ∨ (p1 ∧ ((False ∧ (p2 → p2)) → p5))) → p5)))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111113765541537344839397267528 : (((((((p2 → (p4 → (p5 ∨ p3))) ∨ p2) ∧ p1) → p5) → (((((p4 ∧ False) ∧ p3) ∧ (p4 → p3)) → p1) → p2)) ∧ True) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52023090095384194024781062723 : (((False ∨ (p1 ∧ (((False → p5) ∧ (((p3 → p2) ∧ (p1 → False)) ∨ True)) ∨ p4))) ∨ (False ∧ ((p1 ∨ (p3 → p3)) → (p2 → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_132791353472108213934780291564 : ((p2 ∨ ((((True ∨ p2) → (((p1 ∧ False) ∨ p5) ∨ (True → ((p4 → p1) → p1)))) → (p5 ∧ (p1 → False))) ∨ True)) ∧ (p3 ∨ (True ∨ False))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256941276889576269696790975198 : ((p1 ∨ p5) → (((p4 ∧ (((((p4 → p5) → p3) ∨ True) → False) → ((p2 ∨ p1) → (p5 → (p5 → ((p2 ∧ False) ∧ p4)))))) ∨ True) ∨ True)) := by
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
theorem thm_5_vars_251676175310806087923716970468 : ((p3 → p2) ∨ (((p2 ∧ ((False ∧ (True ∧ p5)) ∧ (p3 → (p2 → ((False ∧ (p5 ∧ p1)) ∨ p4))))) ∧ False) ∨ ((True ∨ (p3 ∧ False)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646076348306652343297348496904 : ((((True → (False ∨ ((((p3 → ((True ∨ True) ∨ p2)) → (False → p3)) ∧ (p2 → (p1 → p2))) ∧ ((p4 → p2) → (True ∧ p3))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326144262057367293465176924648 : (p5 ∨ (p1 → (p4 ∨ ((((p2 ∨ p3) ∧ p5) ∨ ((((p3 → p2) → (p2 ∨ False)) ∧ ((p3 ∧ False) → (p5 ∧ p2))) ∨ (False → False))) ∨ p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150301984965807079627816957528 : ((p4 → (((((False → True) ∧ p2) ∧ p2) → (p4 ∧ p5)) ∧ (((p5 ∨ p2) ∨ p1) ∧ (True ∨ (p3 ∧ p3))))) ∨ ((False ∨ (True ∨ p3)) ∨ p3)) := by
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
theorem thm_5_vars_218287227481340255961859710381 : (((p3 ∨ p3) ∨ (p1 ∧ p4)) → ((p1 ∧ p2) ∨ ((((p5 → p3) ∨ False) ∧ p4) ∨ ((True ∨ ((p3 → p3) ∨ ((p4 ∧ True) → p5))) ∨ p2)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
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
theorem thm_5_vars_315656092712075706734157644777 : (p3 ∨ ((p2 ∧ p2) ∨ ((((False → p4) → (((p3 ∧ True) → (p2 → p4)) ∧ False)) → (p5 ∨ ((p5 → ((p1 ∧ p2) ∨ p1)) ∧ p5))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299224728780111140723143731497 : (False ∨ ((((((p2 → (p3 ∨ p3)) → ((True ∧ (p5 ∧ (True → p1))) → (p4 ∧ (p3 ∧ p5)))) → p4) ∨ (p5 ∨ False)) → (p1 ∨ True)) ∨ p3)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_389722100292298264008802339468 : (((((((((p5 ∧ ((p4 ∨ p1) ∨ p1)) ∧ False) ∧ True) ∧ p2) ∨ p5) ∨ (p2 ∨ (False → ((p1 ∧ (p2 ∨ (p1 ∧ p1))) ∧ p4)))) ∨ p5) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33696995412066068042015772241 : ((p5 ∨ ((((((True ∧ p1) → (p5 ∧ (p3 ∧ p3))) ∧ True) ∨ (((p2 ∧ (p4 ∨ (p4 ∨ True))) ∨ True) ∨ p4)) ∨ (p3 ∧ p3)) ∨ p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_25329075783106795005599632787 : ((((p5 → p3) ∨ p4) → ((((p4 ∨ ((p5 → (p3 ∧ (False ∨ p3))) → ((p3 → (p3 → p3)) ∨ p2))) ∧ p1) → (p5 ∧ p3)) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257803541288177049682048341563 : ((p3 ∨ p5) → ((((((p5 → (False ∨ (p1 → p5))) → (True → (p3 ∧ p2))) ∧ ((p2 ∧ p4) ∨ (True ∧ True))) ∨ p1) ∨ True) ∨ (p2 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340737918377070563306279316102 : (p2 → ((((True ∧ ((p5 → p2) ∨ ((((p4 ∨ (p5 ∧ ((True ∧ p5) → ((p5 → p2) ∧ True)))) ∨ p5) → p2) ∨ True))) → p3) ∨ p4) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



