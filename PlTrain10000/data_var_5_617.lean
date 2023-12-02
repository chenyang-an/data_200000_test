variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314564292015712241701324480725 : (p3 ∨ ((p5 ∨ (p2 ∧ (((((True → p4) ∧ (p2 ∧ (False → True))) ∨ p4) ∨ (p2 ∧ p4)) ∨ False))) ∨ ((False ∧ p5) → (True ∨ (p4 ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_481514922235016419937436813340 : ((((p3 ∨ ((p3 ∨ ((True ∧ False) ∨ p5)) ∨ p2)) ∨ ((((True ∨ p5) ∨ (True ∧ p1)) ∧ p5) → ((p5 ∨ p4) ∧ (p1 → (p1 ∨ p5))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Implications on the right can always be decomposed.
  intro h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h18
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317932775755970015819135688554 : (p4 ∨ ((p1 ∨ ((p5 ∧ ((p5 ∧ (False ∨ True)) ∧ (True → (((p4 → p4) ∧ (((p1 ∧ False) → True) ∧ p5)) ∨ p3)))) ∨ (True ∨ p3))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_49332965417524946010198511971 : (((p5 ∨ ((p3 ∨ p3) ∧ ((p1 ∨ p3) ∨ (p3 ∧ (True → (p4 → (True ∨ (p4 ∧ ((p5 ∧ p4) ∨ p1))))))))) ∨ (p4 → (p2 → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230486959453851582099967934063 : (((True → False) ∧ True) → ((((p2 ∨ ((((p3 ∨ (p4 → True)) → ((p3 ∧ p4) ∧ p3)) ∧ p5) ∨ (p1 ∨ p5))) → p3) ∨ (p4 ∧ p4)) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731995495733091058175098905436 : ((((True ∧ True) ∧ (p3 ∧ ((True ∧ ((p2 ∨ (((True ∧ p1) ∨ True) ∧ p3)) → ((p1 ∨ p5) ∧ p3))) ∧ (p4 → (p4 ∧ (p3 ∧ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353835401563633763951084566927 : (p4 → (p1 → (((((p4 → p1) ∨ False) → ((p3 → (True ∧ (((False ∧ (((p4 → p5) ∧ False) → True)) ∨ p5) ∨ False))) ∨ p3)) ∨ True) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77090691782189160329486981095 : (((((p3 ∨ (p2 ∧ p3)) ∨ p3) ∨ ((((p1 → False) ∧ p4) ∨ True) ∨ ((p2 ∨ (p5 → ((False ∧ (False ∨ p3)) ∧ p4))) → p1))) → p3) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 ∨ (p2 ∧ p3)) ∨ p3) ∨ ((((p1 → False) ∧ p4) ∨ True) ∨ ((p2 ∨ (p5 → ((False ∧ (False ∨ p3)) ∧ p4))) → p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309930014630537283491653055534 : (p2 ∨ ((((p4 → False) → p1) ∨ ((((True ∨ p3) → ((False ∧ p1) → True)) ∧ True) ∧ (p1 ∧ p4))) ∨ (((p2 → False) ∨ (p3 ∧ True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165272048076466781970733700018 : (((((p5 ∨ (((p2 ∧ p2) ∨ p5) ∨ p1)) ∧ (p4 ∧ (p2 ∨ True))) → p2) → (False ∧ p3)) ∨ (p1 → ((p1 → p2) ∨ (p1 → (p1 → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59279597366186114278325143431 : (((p3 ∨ p2) ∨ ((p2 ∧ (p3 ∨ ((True ∨ p1) ∨ (p1 → p2)))) ∨ (((((((p4 ∧ p5) → p1) → p1) ∧ p2) ∧ p2) → False) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313820327105871308962205369991 : (p3 ∨ (((p5 ∧ (((p3 ∧ False) ∨ (((p1 ∧ ((p4 ∧ p3) → p5)) ∧ True) ∧ (p5 → (True ∧ (p2 ∨ p5))))) → False)) ∨ True) ∧ (True → True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710748412217769670005198670586 : ((((((p5 ∨ False) → True) → (False → p3)) ∧ (((False ∨ ((p2 ∨ ((p1 → False) ∨ True)) ∨ True)) → (p3 → ((True ∧ p4) ∨ p4))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319264670655056008716665348561 : (p4 ∨ ((((False ∨ ((p4 ∧ (p5 ∨ p1)) → (((False ∨ p4) ∧ p5) ∨ p4))) ∨ False) ∨ p1) ∨ (p3 ∧ ((p5 ∨ ((False ∨ False) ∧ p4)) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172072427835485210817586688084 : ((((((p4 ∧ (False → p3)) ∧ (True ∧ p1)) → False) → (False ∧ p5)) → (False ∧ p4)) ∨ (p4 ∨ (((p5 → p5) ∨ (False ∨ p3)) ∨ (False ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659534139294367714202947382289 : ((((((((p2 → ((((p3 ∨ p1) ∧ (p2 ∨ p5)) → (p3 ∧ p2)) ∨ p2)) ∨ p2) ∧ (True → p4)) → (p2 → p4)) ∧ p1) → (p2 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146908586955270813662120690929 : (((((((p2 ∨ p2) → p2) ∧ (((p4 → p3) ∧ (((p2 ∨ p2) ∧ p5) → True)) ∧ p5)) → p4) ∧ p4) ∧ p5) ∨ (False → ((p4 ∨ p5) → p5))) := by
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
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117361538738806808110829190047 : ((False ∧ (p1 ∨ ((p1 ∨ (False ∨ False)) ∧ (False → (((p1 ∨ p5) ∧ p2) ∧ ((p4 ∨ (((True ∧ p1) ∨ p5) ∨ p3)) ∧ p4)))))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264210106424619815767512608116 : (True ∧ ((p4 ∨ ((True → True) → (p2 ∨ (False ∧ p4)))) → (((p5 ∨ p3) ∨ (p2 → (((p1 ∧ (p5 ∨ True)) ∨ (p1 ∨ p4)) ∨ False))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_111680031545744255765161823035 : ((((((True → ((False ∨ (p5 ∧ True)) ∨ (p5 → ((False ∧ p3) ∨ p4)))) → (False ∨ (False ∨ (p5 ∧ p1)))) ∧ p2) → p4) ∨ p1) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344201692992511579549995795169 : (p2 → (p1 ∨ (True ∧ ((((p1 ∨ (True ∨ ((p4 ∨ p3) ∨ (True ∧ (p1 ∨ p1))))) ∨ False) → ((((p4 ∨ p5) ∨ True) → p3) → p4)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62085524609762335001804977675 : ((p2 ∧ (p3 ∧ (((False ∧ (p1 → ((p4 ∧ ((p4 → p3) → (p4 ∨ (p4 → (True ∧ (p5 ∨ False)))))) ∧ p4))) ∨ (p4 ∧ p4)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197120006527599805624173688748 : (((p2 ∨ (((p5 ∨ p3) ∨ p2) ∨ p4)) ∨ p4) ∨ (((p4 → ((p2 ∨ (p1 ∨ ((p4 ∨ True) ∧ p4))) → ((True → p3) → p3))) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201117907551053252629032047591 : ((True → (False ∧ (p2 ∨ ((True ∧ p3) ∧ p2)))) → (((p5 ∨ True) → ((((False ∧ True) ∨ p4) → (False ∧ ((p1 → p3) ∧ p3))) ∨ False)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225163344029528634081024948753 : (((p3 ∧ p5) ∧ False) ∨ (p3 ∨ ((((p2 → (p5 ∨ (((p1 → p3) → p2) ∧ p3))) ∧ True) ∧ ((((p4 → False) ∨ p1) ∧ p4) ∧ True)) → p1))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216803102516645099463603890710 : (((p1 ∧ (p4 → p2)) ∧ p4) → (p5 → (p2 → (((p3 ∧ ((((p4 ∧ p4) → (p2 ∧ False)) → p4) → p3)) ∨ ((p2 ∧ p1) ∨ p4)) ∧ p1)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777421155006291267012651161478 : (((p1 ∨ ((((((p5 ∧ True) ∨ p3) ∨ (True → (p1 ∨ p2))) ∧ (p5 → False)) ∨ (False ∨ p4)) ∨ (p1 ∧ (((True ∨ p3) ∧ p4) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320428022613867227579568846628 : (p4 ∨ ((False ∨ p5) → ((False ∧ (p5 ∧ ((p4 ∨ (True ∧ p3)) ∧ (p1 ∧ (p4 ∨ p1))))) ∨ (p3 → ((((p4 → False) ∨ p5) → p4) → p4))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : ((p4 → False) ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58264268281360546109964528164 : (((p5 ∧ p3) ∧ (p3 → ((p4 ∨ ((p1 → (p1 ∧ (((False ∧ p3) → ((p1 → p1) ∧ p3)) ∨ ((True ∧ True) ∧ p1)))) → p2)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307131578606733547469692990332 : (p1 ∨ (False ∨ (((p2 ∧ ((True ∧ p1) ∨ (((False ∧ ((p4 ∧ p1) → (p3 ∧ False))) → (p1 ∨ p5)) → p3))) ∨ (p2 → True)) ∨ (True ∨ False)))) := by
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
theorem thm_5_vars_196921614063395743051207168424 : (((((p4 ∧ False) ∨ (p1 → False)) ∧ p1) ∨ p1) ∨ ((p3 ∨ (((p2 ∧ p4) → (p2 ∧ p3)) ∧ (p4 ∧ (False ∧ p1)))) ∨ (p4 → (True ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60150161076509001350384312193 : (((p4 ∨ p3) → (((p2 ∨ (p3 ∨ (((p1 ∨ (p3 → p4)) ∧ (p3 → p2)) → p2))) ∨ (p5 ∧ (True → (p3 ∧ p3)))) → (p4 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301801005512514495607333894545 : (False ∨ ((p4 ∧ p5) ∨ ((p5 ∧ (p1 ∨ True)) → ((((True → True) ∨ p5) ∨ p2) → (False ∨ ((p5 ∧ p5) ∨ ((p2 ∨ True) ∨ (p2 ∨ False)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      let h5 := h1.left
      let h6 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h5
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h5
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h1.left
      let h11 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h10
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h10
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h1.left
    let h16 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h15
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h15
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116657099832511391803151110593 : (((p3 → p5) ∧ ((((((((p1 ∨ p2) ∧ (p1 → p4)) → p1) ∨ (False ∧ False)) ∨ ((p4 ∨ p2) ∨ False)) ∧ p5) ∧ p4) → p3)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191774188358955368334259068925 : ((p1 ∨ (((p5 ∧ p2) ∧ p4) ∨ (True → (True ∧ p4)))) ∨ (p5 → ((((p5 ∨ p5) ∨ p4) ∨ p2) ∨ (((False ∧ p3) → (p1 → p4)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346587469582395470274567783495 : (p3 → (((p1 ∨ (False ∨ (p2 ∧ (((False → (p1 → p5)) → (p2 ∧ (p2 → (False ∧ p4)))) ∨ (True ∨ True))))) ∧ False) ∨ (False → (p4 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138059876427640297353028476904 : ((True → (p5 ∧ (((p5 ∨ p2) ∧ (((p5 ∨ p3) ∧ p3) ∨ p4)) ∧ ((((False ∨ (False ∧ p4)) ∧ p3) ∨ p4) ∧ p2)))) ∨ (p2 → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_823981156917419515080901941330 : ((((((p2 ∨ p5) ∧ (False ∧ p4)) ∨ ((True → p4) ∧ (False ∨ ((p5 ∨ (p2 ∧ ((p3 ∧ p1) ∨ (p5 ∨ (True → p4))))) → p2)))) ∧ p1) → p4) ∧ True) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h6.left
      let h12 := h6.right
      -- False on the left can always be used.
      apply False.elim h11
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h19 := h14 h18
      -- One of the premise coincides with the conclusion.
      exact h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149804314183551318478611313785 : ((False ∨ (p1 ∨ (((True → (p2 ∨ (((False → True) ∨ (False → ((True ∧ p2) ∧ False))) ∨ p2))) → p1) ∧ p3))) ∨ (((p4 ∨ p2) ∨ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134593671770221026466761018118 : (((((True ∨ (True ∧ (p3 → (((p3 → p3) ∨ (p4 ∨ (p5 ∨ (p4 → True)))) ∨ p4)))) ∨ p3) → (p3 ∧ p2)) → p4) ∨ (True ∨ (p3 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52469797459123978383483093412 : (((p3 ∨ ((((True → (True ∧ (p4 ∨ p3))) → p5) → (True ∨ p1)) ∨ p4)) ∧ (((p5 → (p2 ∨ (p4 ∨ (p3 ∧ p3)))) ∧ p4) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310118124735526203292881560995 : (p2 ∨ (((True ∨ ((((p5 → p5) → p2) → ((p4 ∧ p5) ∧ False)) ∧ p5)) → p3) ∨ (((((p2 → p5) → True) → p3) ∧ p2) → (p1 ∨ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245039792046873712836108938630 : ((p1 ∧ p5) ∨ (((((p3 ∨ p4) ∧ (p3 ∧ ((p5 → p4) ∨ (p3 ∨ False)))) ∧ (False ∧ False)) ∧ (True → (True ∨ (p4 ∧ (p5 ∨ p2))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775947883311381243785561891589 : (((False ∨ (p2 → (((((p3 → ((p3 → (p1 → (p2 → p4))) → (p5 ∧ p5))) ∨ (p3 ∨ p4)) ∨ ((False → False) ∨ p5)) ∧ p2) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208966974737341662806969601814 : ((True ∨ ((False ∧ p2) → (p3 ∨ p4))) → ((p3 → (p1 ∨ (((p2 ∨ (p1 ∨ p3)) ∨ (True ∨ (p1 ∨ p2))) ∨ p1))) ∧ (True ∨ (True ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
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
  case inr h4 =>
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312706060831869778845565394811 : (p3 ∨ (((((((True ∨ p5) ∨ p4) → (False ∨ p3)) ∧ p2) → ((p1 → (p3 ∧ (False ∧ p3))) ∧ p2)) → (((True → p2) ∧ p2) ∨ True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2290422160562725981900341780 : ((True ∧ (((p4 ∨ p4) → False) ∨ (((p4 ∧ p3) ∧ (p5 → p1)) → False))) ∨ ((p4 ∨ (p1 ∨ ((p5 → p3) ∨ (True ∨ p2)))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301030592352755656456738235507 : (False ∨ (((p1 → p4) ∨ ((p1 → (p1 ∨ (p1 ∨ True))) ∨ p3)) ∧ ((True → p1) → ((((True → True) → p4) ∨ False) ∨ (False ∨ (p2 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231136792936244159615307301448 : (((p1 ∨ p3) ∨ p2) → (p4 → ((p2 ∨ (p4 ∧ p2)) → ((((p1 → p4) ∨ p1) → False) → (False ∨ (((True ∧ (p2 ∧ p3)) → p2) → p5)))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h8 : ((p1 → p4) ∨ p1) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h9 := h4 h8
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h11 : ((p1 → p4) ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h12
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h13 := h4 h11
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h15 : ((p1 → p4) ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h17 := h4 h15
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h23 : ((p1 → p4) ∨ p1) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h24 := h4 h23
        -- False on the left can always be used.
        apply False.elim h24
      case inr h25 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h26 : ((p1 → p4) ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h27
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h28 := h4 h26
        -- False on the left can always be used.
        apply False.elim h28
    case inr h29 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h30 : ((p1 → p4) ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h31
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h32 := h4 h30
      -- False on the left can always be used.
      apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118684671325435648221414488646 : ((p5 ∨ (((p4 → ((p2 ∧ p5) → True)) ∧ ((p5 ∨ p5) ∨ (((((p5 ∨ (p2 → p2)) → p2) → p2) → p4) ∨ True))) ∧ p1)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117765401927581700908804223287 : ((p4 ∧ ((p3 ∨ (((p4 ∧ p2) ∨ (p5 ∨ (p2 → p5))) ∨ (True ∨ (p4 → (((p2 → p2) ∧ p3) → (p4 ∨ False)))))) → p3)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113833954661833343756890821619 : (((p1 ∨ (((((p1 ∧ (True ∧ p4)) → p3) ∧ ((p4 → False) ∨ p5)) → False) ∨ (((p1 → p5) → p4) ∧ p4))) → (p1 ∨ False)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248283344567328380441949955578 : ((p2 ∨ p2) ∨ ((False → (p1 ∧ (((p3 → p3) ∨ p4) ∨ p4))) → ((True → p5) ∨ ((p5 ∧ ((p3 → p1) ∧ p4)) ∨ (True ∨ (p2 → True)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116326325544960761733780812662 : ((((True ∨ p5) ∧ True) → ((True ∧ p2) ∨ ((p5 ∨ p1) ∨ ((p2 ∨ (((((p4 ∧ p1) → True) → p4) ∧ p2) ∨ p1)) ∨ True)))) ∨ (p4 ∧ False)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788845142831093692014378023855 : (((p5 ∨ ((((((p4 ∨ False) ∨ (True ∨ ((p3 ∧ p3) ∧ p1))) ∨ (p3 → p3)) ∧ ((p4 → (False ∨ False)) ∧ p3)) ∨ p3) ∧ (False ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159430067563601760836243591219 : (((((((((((p3 → p2) → p1) ∨ False) ∧ False) → p3) ∨ True) ∨ p5) ∨ True) → (p5 ∧ False)) ∧ p3) → (((p2 ∧ True) ∧ False) ∨ (False ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((((((((p3 → p2) → p1) ∨ False) ∧ False) → p3) ∨ True) ∨ p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231033169515874662092203162429 : (((True ∨ True) ∨ True) → (p4 → (p3 ∨ (p1 → ((p5 ∨ True) ∨ (p1 → ((True ∧ (((True ∧ p2) → p5) → (p2 ∧ (p4 ∨ p2)))) ∨ p5))))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167598246003863679857617672115 : (((False ∨ ((p2 ∨ (p3 ∨ ((False ∧ p4) → (p5 ∧ (True ∨ True))))) ∧ p4)) ∨ (p5 → p1)) → ((p5 → p5) ∧ ((p2 → (p3 ∨ True)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h11 =>
          -- One of the premise coincides with the conclusion.
          exact h2
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
  case inr h22 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h23
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606318440289359201612944073044 : ((((((((((p4 → ((p4 ∧ p2) ∨ (p2 → ((p2 ∨ False) → False)))) ∧ p2) ∧ True) ∧ ((p5 ∧ p2) ∨ p5)) ∨ False) ∨ p4) ∧ p1) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_358473033828712393935038886801 : (p5 → (p1 → (((p5 → False) ∧ ((p1 → p5) → (((((((p4 → False) ∨ p2) ∨ p2) → p5) ∧ (p3 ∨ False)) ∧ p2) → p3))) → (False ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h11 := h8 h10
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179151107318981416771057068909 : ((p2 ∧ ((p5 ∧ (((p1 ∧ p5) → ((p1 ∧ False) ∨ True)) ∨ p1)) ∨ p4)) ∨ ((p3 → ((p3 ∧ p1) ∨ p2)) ∨ (False → (p2 ∨ (False ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234899345315092215213310658244 : ((True ∧ True) ∧ (((p3 → p4) ∨ ((p4 → (False ∧ (False ∨ ((((p3 ∨ p5) ∨ ((p3 ∧ p5) → (p2 → p1))) ∨ p4) ∧ p1)))) ∨ p5)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658581869219056724856786715886 : ((((p3 ∨ ((True ∧ (((p4 ∨ ((p2 ∧ ((False ∨ p5) → (p1 ∨ (p3 → True)))) → (False ∧ p2))) ∧ False) ∨ p4)) ∧ False)) ∨ (False → p4)) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248035643141474680405817822373 : ((p1 ∨ p5) ∨ (((((p2 → p1) → (False ∧ p3)) → ((True ∧ p3) ∧ (p2 ∨ False))) ∧ True) ∨ ((((False → (p4 ∧ True)) ∧ True) ∨ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701283909876913352965813607994 : ((((((((False ∨ p2) ∧ p5) ∧ False) → p3) → (p4 ∨ False)) ∧ ((p3 ∧ (p3 ∧ ((True ∨ (p4 ∧ (p5 ∧ p4))) ∧ p3))) → (False ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178690514998166885572212661552 : ((((p3 → (False ∨ p1)) ∨ p2) ∨ ((p5 → ((p1 → p1) → p1)) → p5)) ∨ ((False → False) → ((((p5 → (p1 ∨ False)) ∧ p1) ∨ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597235493281563104534797305900 : ((((((p5 ∨ p1) ∧ (False ∧ p5)) ∧ ((((((p2 → p5) → p1) ∧ ((p5 ∨ (p2 → True)) ∧ p2)) ∧ True) ∧ (p4 ∨ True)) → p4)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148775563800090625744039847873 : ((((p3 ∧ (p5 ∨ False)) ∧ (p1 ∧ p1)) ∨ (p1 → ((p5 ∧ ((((p1 ∨ p2) ∧ p5) ∧ p5) → p3)) ∨ p1))) ∨ (True → (False ∨ (p3 ∧ p5)))) := by
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
theorem thm_5_vars_351563247544730674514436805867 : (p4 → ((((((p5 ∧ ((p1 ∧ (p3 → (False ∧ True))) → p3)) ∧ p5) → p2) ∧ p3) ∧ (p1 → True)) → (p2 → ((False ∨ (p2 ∧ p2)) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h2.left
    let h10 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257565796991020725001842509844 : ((p3 ∨ p1) → (((((((p1 ∧ p2) ∨ p5) ∧ (True ∧ p3)) → p2) ∨ p4) ∨ (p4 ∧ (p2 → (p2 ∨ (p2 ∧ p4))))) → (False ∨ (True ∨ p3)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h5 =>
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
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792223063340060730483002427369 : (((True → ((((p3 ∨ True) ∨ p2) → ((p1 → ((p4 ∧ (p1 ∧ True)) ∧ False)) → ((p1 ∧ p2) → p5))) ∨ (False → ((True → p2) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614562363253596769068536409280 : ((((((p3 → (p4 ∨ (p4 → True))) → (p1 → (((p1 → p1) ∨ (p3 ∧ (False ∧ p3))) ∧ False))) ∧ (((p4 → p3) → p4) → p4)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61814517306722537871767770839 : ((p2 ∧ ((((((p4 → ((p5 ∨ True) → True)) → p3) → p2) ∧ p3) → ((((((False → p5) ∨ True) ∨ True) ∧ p2) ∧ True) → p4)) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47530774318562507620238620847 : (((p4 ∨ ((((p1 ∨ p3) → False) ∧ (((False → (p2 ∨ (p3 ∨ (p3 ∨ (True ∨ p4))))) → p1) → p1)) ∨ (True ∧ False))) ∨ (True ∨ p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41147325411640615440126842820 : (((((((p5 ∧ p5) → p4) → p1) ∧ ((((((False ∨ p2) ∨ (p4 → p3)) ∨ p3) ∧ True) → p4) ∨ p3)) ∨ ((p1 → p1) ∨ p2)) ∨ p1) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114359465271060936277128039060 : (((((p2 ∨ ((((False → p5) → True) ∧ p1) ∧ (p5 ∨ True))) ∧ (p2 ∧ (p3 ∨ p1))) ∧ p5) ∨ (((True ∨ p3) ∧ False) → False)) ∨ (p1 → False)) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691110105611080362205549114662 : (((((p4 ∧ ((False → (p1 ∧ (False ∨ p3))) → True)) ∧ (p1 ∨ ((False ∧ True) ∧ True))) → ((p4 ∧ (p1 ∨ ((True ∨ p5) ∨ True))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310220766773148142376840948650 : (p2 ∨ ((p2 ∧ (((p5 → True) → p1) ∨ (p2 ∨ ((False ∧ p2) ∨ False)))) ∨ ((p5 ∨ (p3 ∧ (((p1 ∨ (p2 ∨ p4)) ∧ p4) ∨ p3))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208609319499779970524827194111 : (((p5 → True) → (True → (p4 → p1))) → (p4 → (((True → p1) ∧ (((p2 ∨ p1) → p5) ∧ (((p3 → p3) → p3) → p4))) ∨ (p3 → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259449936683317811657595590495 : ((False → p4) → (((p4 ∨ p1) ∧ (((((p3 → (((p4 ∨ p1) ∧ p1) ∨ True)) ∧ True) → p2) → p3) ∨ p3)) ∨ ((p1 ∧ p1) → (p1 ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37931730704750671067722226980 : ((((p2 ∧ (True ∧ (((p1 ∨ (False → p3)) → p5) → ((p1 ∨ ((False ∨ p5) ∨ ((False ∨ p1) ∨ p4))) ∧ True)))) ∧ (p5 ∧ p1)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184226078569686238225943778270 : ((((p1 ∧ (p1 → (p2 ∧ (p1 ∨ (p5 ∧ True))))) ∨ p5) → False) ∨ ((((False ∧ False) → p5) ∧ (p1 → p5)) → ((p3 ∧ False) ∨ (True ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259346738850982126516681146201 : ((False → p2) → ((p2 → True) → ((True ∧ p2) → ((((p5 ∧ ((p3 → False) → p2)) ∧ p5) ∨ (False → ((True ∧ p5) → True))) ∨ (p2 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725803384591892459745570609288 : (((((p4 ∨ p1) ∧ p4) ∨ (p4 → (((p5 ∨ p4) → (((p2 ∧ ((p5 → False) ∧ (p4 ∧ p5))) ∨ False) ∨ ((True ∨ p3) ∧ p4))) ∨ p2))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41789296143421707880521786149 : (((((False → (p1 ∧ p1)) → p3) → ((((False → ((p1 ∧ ((p1 → (p1 ∧ p1)) → p2)) ∧ True)) → (True ∧ p3)) ∧ p3) ∨ p2)) ∨ p3) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (False → (p1 ∧ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (False → (p1 ∧ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147759374968054147985981094598 : ((((p3 ∧ (p1 ∧ p2)) → (p4 ∨ ((False → (p2 → (p5 ∧ ((p2 ∧ p4) ∨ False)))) ∨ (True ∨ p5)))) → p2) ∨ (p4 ∨ (p4 ∨ (p4 ∨ True)))) := by
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
theorem thm_5_vars_264447232290413858174288610146 : (True ∧ (((False → p3) → (p5 ∨ False)) → (((p5 ∨ p5) → ((p2 ∧ (p4 ∨ (p2 ∨ ((False ∨ p5) ∨ p4)))) ∧ False)) ∨ ((p3 → False) → True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_469711209114473666504656303329 : ((((p5 ∨ (((((True ∨ True) ∧ p5) → False) → True) ∨ ((p1 → p3) ∨ p4))) → (((p3 ∨ (True ∨ False)) → False) → (p3 ∧ (p4 ∧ p5)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (p3 ∨ (True ∨ False)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : (p3 ∨ (True ∨ False)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h12 : (p3 ∨ (True ∨ False)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h13 := h2 h12
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h15 : (p3 ∨ (True ∨ False)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h16 := h2 h15
        -- False on the left can always be used.
        apply False.elim h16
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h17 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h18 : (p3 ∨ (True ∨ False)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h19 := h2 h18
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h22 : (p3 ∨ (True ∨ False)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h23 := h2 h22
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h26 : (p3 ∨ (True ∨ False)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h27 := h2 h26
        -- False on the left can always be used.
        apply False.elim h27
      case inr h28 =>
        -- One of the premise coincides with the conclusion.
        exact h28
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h29 =>
    -- One of the premise coincides with the conclusion.
    exact h29
  case inr h30 =>
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h31 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h32 : (p3 ∨ (True ∨ False)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h33 := h2 h32
      -- False on the left can always be used.
      apply False.elim h33
    case inr h34 =>
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h35 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h36 : (p3 ∨ (True ∨ False)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h37 := h2 h36
        -- False on the left can always be used.
        apply False.elim h37
      case inr h38 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h39 : (p3 ∨ (True ∨ False)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h40 := h2 h39
        -- False on the left can always be used.
        apply False.elim h40
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114270542546542965392820616102 : ((((p5 ∨ (p3 ∧ (p4 ∧ ((p1 ∨ False) ∨ (p5 → ((p1 → False) ∨ (False ∧ p5))))))) ∧ p1) ∧ ((p4 ∨ p4) ∨ (p5 ∨ True))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259543982270568315051156193291 : ((False → p5) → (p3 → ((((p3 ∧ (p4 → (p5 ∧ p3))) → (((p5 ∨ (p4 → True)) ∧ p5) ∨ (p1 ∧ False))) ∨ False) ∨ (p5 → (p4 → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232502028325416023320289666040 : ((True ∧ (p1 → p1)) → ((p2 ∧ (p1 → (((True → p4) ∨ (p4 → p1)) ∧ p2))) → (True → ((p4 ∨ p2) ∨ ((False → (p3 ∧ False)) → True))))) := by
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
  let h6 := h1.left
  let h7 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57328190985744802988272917355 : (((p1 ∧ (True ∧ p2)) ∨ (p3 → (p4 ∨ ((((p2 → ((p5 ∨ p2) → p1)) → (p4 ∧ (p3 ∨ True))) ∧ (p2 ∧ (p1 ∨ False))) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757855262982594110766153518741 : (((p1 ∧ (p2 ∨ (p2 → (((True ∧ p4) → True) ∧ (((p4 → False) ∧ (((p3 ∨ (p2 ∨ p3)) → (p5 ∧ p5)) ∨ p3)) → (p1 ∧ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228653900121508901933113518781 : ((p2 ∨ (p3 ∧ True)) ∨ ((((p1 ∨ (True → (p3 ∧ (False ∧ (False → p4))))) → ((p1 ∧ (p2 ∨ (p3 ∨ False))) → p5)) → (p3 → p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340945768594219924105465195043 : (p2 → ((((p3 → p3) ∨ p1) ∧ (((p5 → (p1 → p5)) → p1) ∨ (p3 ∨ (((p5 → (True ∨ (p2 ∧ p5))) → (p3 ∨ False)) ∨ p3)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64961567825714435423653767190 : ((p2 ∨ ((p1 ∨ ((p2 → ((p4 ∨ True) ∧ p3)) ∧ p3)) → (False ∨ (p1 → ((p4 ∨ ((p5 ∧ p4) ∨ (p5 ∧ (p2 ∧ p5)))) ∨ p1))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258582692992869960914810275707 : ((p5 ∨ p4) → (((((p4 ∧ ((p1 ∧ ((p4 ∧ p4) → p5)) → p4)) ∧ p1) ∧ p2) ∨ ((True ∧ ((p4 → (False ∧ p5)) ∧ p5)) ∨ False)) ∨ True)) := by
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
theorem thm_5_vars_341995516345215113194844046407 : (p2 → ((((p5 ∧ (p5 ∨ False)) ∨ (p1 ∨ p4)) → (((((p2 → p2) → p4) ∨ p2) ∧ (p5 ∧ True)) ∨ (True ∧ p3))) ∨ (True ∨ (p3 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190433700288725109324521257928 : (((p5 ∨ (p1 ∧ ((p4 → p4) → (p4 ∨ p1)))) ∨ p4) ∨ (((p1 ∨ p1) ∨ ((p2 → p2) ∧ True)) ∨ ((False ∨ (True ∨ (True ∨ True))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_358557210281922954214302395249 : (p5 → (p2 → (True ∧ (p5 ∧ ((p5 ∧ (p1 ∨ (p4 ∨ (p4 → (False ∨ (p3 ∨ p2)))))) → (((p1 ∧ ((False ∧ p4) ∨ p2)) ∧ False) ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



