variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165362397707819664457485687497 : (((p5 → ((((p1 ∧ True) ∨ p4) ∨ (True ∧ p3)) ∨ (p1 ∧ p3))) ∧ ((p1 ∨ p3) ∧ p4)) ∨ (((p4 → p4) → True) ∨ ((p2 ∧ True) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147826896680303046063480557833 : (((False ∨ (((p5 → p4) → True) → (((p5 → ((p1 ∧ False) ∨ (p3 → True))) ∨ p5) → (False ∨ p3)))) → p5) ∨ (False → ((True ∨ p1) → p2))) := by
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
theorem thm_5_vars_740384242086318061564314729383 : ((((p1 ∨ p2) ∨ (p5 ∨ (((p5 → p2) ∨ ((((p4 ∨ p5) ∧ (True → p3)) ∨ p2) ∨ (p5 ∨ (p4 ∨ (p3 ∧ True))))) ∨ (False → p3)))) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749457763596661294553342129235 : (((True ∧ (((False → ((True → p1) ∧ ((True ∨ p2) ∨ ((p1 → p5) ∨ p2)))) → (p1 → (((p5 ∨ False) ∧ (p2 ∨ False)) → p5))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601869156539248181748432842231 : ((((p4 ∧ (((False → p1) ∧ (p3 ∧ p3)) → ((((((True → p2) ∧ p4) → False) ∨ p5) ∨ ((p2 ∧ p3) ∧ (p2 ∨ p4))) ∧ p2))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172567620345641806014051152102 : (((p3 ∨ (p2 ∧ p5)) ∨ (((p5 ∧ (p1 ∧ (p4 ∧ p4))) ∧ True) ∨ (p2 → p5))) ∨ (((p2 ∨ False) ∧ (True ∧ p5)) → (True → (p5 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    let h6 := h4.left
    let h7 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739610662270285746894508808925 : ((((p5 ∧ p4) ∨ ((((p1 ∧ p2) ∧ p1) → ((True ∨ ((p4 ∧ (p1 ∨ ((True → (True ∧ p1)) → p1))) ∧ p4)) ∧ (p1 ∧ p3))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623891157536281829708040883503 : ((((p1 ∨ (True → (((p3 ∧ p3) ∨ p3) ∨ (((True ∧ p5) → (((p4 ∨ (False → (p4 → True))) ∧ (p4 ∨ p3)) ∧ p4)) ∧ p3)))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_113441689072061883521013975191 : ((((((p1 ∨ p5) ∨ False) ∧ (p4 → ((p3 → (p2 ∧ p4)) → (p1 ∨ (((p1 ∨ p1) ∧ p4) ∧ p2))))) ∨ p4) ∨ (p5 ∧ p3)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118445353404807365614749716353 : ((p3 ∨ (((p4 → (True ∨ (p5 ∨ ((True → ((p2 → ((p5 ∧ p5) ∨ (p2 ∨ (p1 ∨ False)))) ∧ p1)) ∨ p1)))) → p5) ∧ p4)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57505015391306331806528889787 : (((p3 → (False ∧ p2)) ∨ ((p3 ∧ ((False ∧ False) ∧ ((p4 → ((p3 ∧ p4) → (p5 ∧ p2))) ∧ p3))) ∧ (p3 → (False → (p4 ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586270511865409779645896088059 : ((((((True → (p3 ∨ ((p4 → ((True → p5) ∧ p3)) ∧ p5))) → (False ∨ ((p3 ∨ (p3 ∨ p2)) → ((False → p5) → p1)))) ∧ p3) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115412848341671194343657504494 : (((p3 → (False ∧ ((p5 ∧ (p3 ∧ False)) ∧ p2))) ∧ (((False ∨ (True ∧ (True ∧ p4))) ∧ ((p4 ∧ p5) → True)) ∧ (p2 → False))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328654179703149441897043344427 : (True → ((p1 ∧ (True → (p1 → ((((False → (p3 → p2)) ∧ False) ∨ p3) ∧ True)))) → (((p1 ∨ (p5 ∧ (False ∨ (p2 ∨ True)))) → p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344778831812617476084437368057 : (p2 → (p4 → (((((((p3 → p1) → (p5 → False)) ∧ p5) ∨ (p2 ∨ (p1 → p4))) ∨ p4) → (False ∧ (p5 ∨ ((p5 ∧ p4) → True)))) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((((p3 → p1) → (p5 → False)) ∧ p5) ∨ (p2 ∨ (p1 → p4))) ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316991482532821773408045465006 : (p3 ∨ (p3 → ((True → ((p1 → ((p5 ∨ (p4 ∧ p1)) ∨ ((p4 ∧ p4) ∧ True))) ∧ ((p3 → p4) → False))) ∨ (p1 → ((p1 ∨ p2) ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43260672913132012974337165968 : ((((p2 → ((p5 ∨ p5) ∧ ((((((p4 ∨ (p2 ∨ p4)) ∧ False) ∨ ((False ∨ p5) → p2)) ∨ p1) ∧ True) ∧ (p3 ∧ p4)))) ∧ p5) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596315006953279842057583687031 : (((((((((p3 ∨ p1) ∨ p3) → p1) ∧ p1) ∨ p1) ∨ (p3 → ((((p5 ∨ True) ∨ p3) ∧ (False ∧ (True ∧ (p5 → p5)))) ∨ False))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245403559798469286801219166234 : ((p2 ∧ p4) ∨ (((p2 → ((p3 → (p3 → ((((p5 ∧ p2) → p3) → ((p2 ∨ False) ∨ (p5 ∧ p1))) → p4))) ∨ p2)) ∨ (p3 ∨ True)) ∨ False)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324082701404489745620747926963 : (p5 ∨ ((((p1 → (p1 ∨ p2)) → p4) ∨ (((p1 → p5) ∧ p2) ∧ p1)) ∨ ((p3 ∧ ((p4 → p2) ∨ (p4 → (p2 ∨ p3)))) ∨ (p3 → True)))) := by
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
theorem thm_5_vars_112255673382075390205377211752 : (((p4 ∨ ((((True ∨ (False ∧ p4)) → p4) ∨ False) ∧ ((True → p1) → (((p1 ∨ p5) → ((p1 ∧ p3) → p1)) → p4)))) ∨ p1) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158606257702189382784197524820 : ((False ∧ ((p5 ∧ ((((p4 ∧ (p1 ∧ p5)) → False) ∨ p5) → (p4 → True))) ∨ ((p2 ∧ p2) ∧ p1))) ∨ ((True ∧ (True ∨ True)) ∨ (p2 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306019596105801055999851190364 : (p1 ∨ ((p4 ∨ ((p4 ∧ p3) ∨ p5)) ∨ ((p2 ∨ ((p1 ∧ False) → (p2 ∧ ((((True ∧ p5) ∨ (p2 ∨ (False ∧ p1))) ∨ p3) ∨ True)))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310487694988123453643558482544 : (p2 ∨ ((((p5 ∧ (p1 ∧ False)) ∨ p2) ∨ p3) ∨ (((((p2 ∧ ((False ∧ (p5 ∧ True)) ∧ True)) ∧ p1) ∧ (p1 ∨ p2)) → p2) ∧ (False → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- False on the left can always be used.
  apply False.elim h10
  -- Implications on the right can always be decomposed.
  intro h12
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138162723664713978833241830179 : ((p1 → ((p4 ∨ (((((((p5 ∨ p1) ∨ p2) ∧ ((True → p4) ∨ True)) → True) ∧ p1) ∨ False) ∧ p1)) → (p5 ∧ True))) ∨ (False → (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137693007279072124155224343974 : ((p1 ∨ ((True ∧ (True → (p1 ∨ (True → ((p5 ∨ (p1 ∧ p4)) ∨ ((p2 → ((p2 ∨ True) ∧ p1)) → p2)))))) → p1)) ∨ ((True → True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204462992791711996730420793963 : ((((p4 ∨ (p1 ∧ p2)) ∧ p4) ∨ False) ∨ (p3 ∨ ((((p1 ∧ (p3 ∧ p5)) ∧ (p3 ∨ False)) ∨ False) → (p4 → (p2 → (p5 ∨ (p1 ∧ p5))))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654427468696881972394959663629 : ((((((p5 ∨ (True ∨ p1)) ∧ ((True → p3) ∨ ((((True → ((p1 ∨ (p3 ∨ p2)) ∨ p3)) ∨ p3) ∨ p1) ∧ p1))) ∨ True) ∨ (False → p1)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_54241596983277361502667301297 : (((((True ∨ (p4 → True)) ∨ True) ∧ (False → p4)) ∧ (False ∨ (((((p5 → p1) ∨ p3) ∨ ((False ∨ (False → p5)) ∧ False)) ∨ p5) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161011965689924025487794067847 : (((p3 ∧ (p1 → p2)) ∨ (p2 ∧ (((((p3 ∧ (p1 → False)) ∧ p1) ∨ (False → p2)) ∧ False) ∨ p4))) → (p5 ∨ ((False ∧ (p5 ∨ True)) ∨ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h12.left
        let h15 := h12.right
        -- False on the left can always be used.
        apply False.elim h10
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338065657062309071597262622076 : (p1 → (((((p5 ∧ p2) ∨ (p5 → True)) → p3) ∧ (p4 ∨ p1)) → ((p3 ∧ (((p1 ∧ True) → p4) ∧ True)) → ((p5 ∨ p5) → (p4 ∨ False))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h2.left
    let h11 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h14 : (p1 ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h1
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h15 := h8 h14
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h3.left
    let h18 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h2.left
    let h22 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h24 =>
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h25 : (p1 ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h1
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h26 := h19 h25
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3227361223626717017240127139 : ((p1 ∨ p3) ∨ ((p5 ∧ (p4 ∧ ((True ∧ p2) → p5))) ∨ ((True ∧ ((((p2 ∧ p3) ∨ p1) → p5) ∨ (True ∨ p2))) ∨ (p5 ∧ p5)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67594371092704077180022104704 : ((p1 → (False ∧ ((((((p3 → p3) ∨ True) ∨ (p4 ∧ (p3 ∧ ((p2 ∨ (p5 → ((p3 ∧ p4) → p2))) ∧ False)))) → p4) ∧ True) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158070182985294002511424679755 : ((((p4 ∨ (p5 → (p1 ∨ p5))) ∨ p5) → (p5 → (((((True ∨ p1) ∨ True) → False) ∧ False) ∨ True))) ∨ (((p3 → p5) → (p5 ∧ p5)) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756119535831840764942817413997 : (((p1 ∧ (((((p5 ∨ (p1 ∨ True)) ∧ (((p1 ∨ True) ∧ p3) ∧ True)) → (p5 ∨ (False ∨ (False ∧ (p3 ∨ p4))))) → p1) ∧ (p5 → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347282673050729218235463841050 : (p3 → (((((p3 ∧ p4) ∧ (p1 ∧ True)) ∨ p1) ∨ (False ∨ False)) ∨ (p5 ∨ (((True → p4) ∨ (p3 ∧ (p1 ∨ p3))) ∨ (False ∨ (True ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246307637706261038931777417391 : ((p4 ∧ p5) ∨ ((((True → ((p5 ∨ (((False ∧ (False → False)) ∨ (True ∧ (p1 → (p1 ∧ (True ∨ p5))))) ∨ p2)) → p1)) ∨ p5) ∨ True) ∧ True)) := by
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
theorem thm_5_vars_116478899674129198738856113643 : (((p1 ∧ p4) ∧ (((p4 ∨ (p2 ∧ (((p5 → p5) ∨ (((p2 ∧ (p4 ∧ p2)) ∧ (p1 → True)) ∧ p5)) → p5))) ∧ p1) ∧ p4)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710747474255451941997767485841 : ((((((p3 ∨ p4) → p3) → (True ∨ False)) ∧ ((True → ((((p2 → p3) ∨ p4) ∨ True) ∧ ((((p1 ∨ True) ∨ False) ∧ p4) ∨ p3))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214312790330801244595591582839 : (((True ∨ (p5 → p2)) → p3) ∨ ((((True → p2) ∨ (((False ∧ (p5 ∨ True)) ∨ (p4 ∨ ((p1 → p1) ∨ p1))) ∨ (False → True))) ∨ p1) ∨ p5)) := by
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
theorem thm_5_vars_114672196322469796283626174591 : (((True ∧ ((((((p3 → p4) → (p1 ∨ (p5 ∨ p2))) ∧ p5) ∧ True) → p5) → p5)) ∨ ((p3 ∧ p3) ∨ (p1 → (p5 ∨ True)))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49066997786717793333197472216 : (((((p2 ∧ False) ∧ ((False ∨ ((False ∨ (p5 → p4)) ∨ (((True ∨ True) ∧ p5) ∨ p5))) ∧ p3)) ∨ (True ∧ p3)) ∨ ((p4 ∨ True) ∨ p3)) ∨ False) := by
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
theorem thm_5_vars_18304293404569785148188099118 : ((((((p2 → p3) ∨ p4) ∨ (p2 ∧ p2)) ∧ (((True → (((p1 ∧ p1) ∨ p2) ∧ p3)) → True) → False)) → (False ∨ ((True ∧ p5) ∨ True))) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113591991346670240016507759347 : (((p5 ∧ (((p1 → (True ∧ p4)) ∧ (p2 ∨ (((((True → p3) ∨ False) ∧ p5) → (p2 ∧ False)) ∧ p1))) ∧ p1)) ∨ (p5 → False)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50416718948017234314829057360 : (((p2 ∧ ((((((p1 → False) → p5) ∨ p5) ∧ (p4 ∧ p4)) ∨ ((p1 → (p5 ∨ p4)) → p2)) → p1)) ∨ (((False ∨ p1) ∧ p1) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257629605009872246724655936034 : ((p3 ∨ p2) → (((True → ((False ∨ p2) → ((p4 → p5) ∨ (p5 → (p2 ∧ p4))))) ∨ (p5 → True)) ∨ (((True ∧ p1) → False) ∧ (p3 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179196745104273992509280129826 : ((p3 ∧ (p2 ∧ (((True ∨ (False → p3)) ∧ (p2 ∧ p4)) → (False ∧ True)))) ∨ ((((p1 ∨ (p4 ∧ p4)) ∨ p3) ∨ p3) ∨ (False ∨ (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671240213326185042696110606596 : ((((p4 ∨ ((((((p5 ∧ False) ∨ (True → p3)) → True) ∨ p4) → (p2 ∧ (p4 → p3))) → (p5 ∨ (p1 ∨ p5)))) ∨ ((p3 ∧ False) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167017532119086725707681093757 : (((p4 → ((((p1 ∧ (False → p2)) → p1) ∨ (p3 ∨ False)) → ((p1 → p5) → p3))) ∧ True) → ((p5 ∧ (False ∨ (p5 → p4))) ∨ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659154747414444392285650219177 : ((((p3 → (((((p5 ∨ (p3 ∨ (False ∨ p1))) ∧ p5) ∧ False) → True) → (p4 ∨ ((p2 ∨ p1) → ((p4 ∧ False) ∧ p1))))) ∨ (False → p1)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_788536687273358154601719731454 : (((p5 ∨ ((True → (p1 ∨ (p4 ∨ ((p4 → p1) ∨ (False ∨ (((p2 ∧ ((True ∨ False) ∧ p2)) → (p2 → True)) ∨ (p2 → p3))))))) ∨ p4)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_115806122224799946752294553456 : (((((False ∨ p3) → p4) → p2) ∧ ((p4 → (True → (False ∨ (p3 ∧ (p2 ∧ p5))))) → ((p5 → (p1 ∧ p2)) ∨ (p5 → p2)))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166150751510921999997023926273 : ((False ∧ ((((p1 → (True → (p3 ∨ p3))) → p1) ∧ (p5 ∨ ((True ∨ p5) → p5))) ∨ False)) ∨ (((False → (p4 ∨ (p4 → p3))) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59812534338465809412102882053 : (((p3 ∧ True) → ((False ∨ ((p4 ∧ ((((((p4 ∧ p5) → False) → (p5 → p5)) ∨ p3) ∨ (p4 ∨ p4)) → p3)) ∧ p1)) ∧ (p1 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41138635489608054781290119730 : ((((((((p4 ∨ p4) ∧ p5) ∨ (p4 ∧ ((p3 ∧ (p3 ∨ p3)) → p4))) → (p3 ∧ True)) → (p1 ∧ False)) ∨ (p2 ∧ (False ∨ p2))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313276240013782147199963162563 : (p3 ∨ ((p2 ∧ ((p2 ∨ (p3 ∧ (((p5 ∧ (p1 → p1)) ∧ p3) ∧ ((True → p1) ∧ ((p2 → p2) ∨ p4))))) ∧ (p2 → (p2 ∧ p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301006198876352930644378991100 : (False ∨ ((False ∨ (p2 ∨ (((False → True) → p4) ∧ ((p1 ∨ False) ∨ p1)))) → ((((p1 ∧ (p1 → p4)) → p3) → True) → ((p3 ∨ p2) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- False on the left can always be used.
          apply False.elim h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137953557295133667016858081562 : ((p5 ∨ (((p2 → ((p2 ∧ p4) ∧ (p2 ∧ ((p3 ∧ (True ∧ (p1 → ((True ∨ True) ∧ p4)))) → p2)))) ∧ p4) → p3)) ∨ (p2 → (p5 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50948620702555405741714667739 : (((((p5 ∧ (p3 ∨ (p2 → p3))) ∧ (p5 ∨ p5)) ∨ ((p1 ∧ p2) → (p2 ∧ (p3 → False)))) ∧ ((p2 ∧ p3) ∧ ((p2 ∧ True) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158854003791121516955182009226 : ((False ∨ (((p4 ∧ ((p2 ∨ (True → ((p1 ∧ True) ∨ (p2 → False)))) ∧ p3)) ∨ (p3 ∧ p1)) ∧ p1)) ∨ ((p4 → ((p2 → True) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319552624508061529561619580645 : (p4 ∨ (((p5 ∨ p2) ∨ (p4 → ((p3 ∨ False) ∧ (p1 ∧ p1)))) ∨ ((True → True) → ((False ∨ (p5 → True)) ∨ (p1 → (p5 → (True ∨ False))))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134857848959248196487301351180 : (((True → ((p1 ∧ (((p4 ∧ (p5 → (p2 → False))) ∧ True) ∧ (p1 ∧ p1))) → ((p5 → p3) ∨ (p4 → True)))) → False) ∨ (p3 ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_452082710539721856057058966573 : (((((True ∨ False) ∧ ((((True → (p2 ∨ p3)) → p3) ∨ p3) ∧ (p4 ∧ (p5 → (False ∨ (p1 ∨ p3)))))) ∨ (p5 → ((p3 → True) ∨ p5))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735525622389451089935895290414 : ((((p4 ∨ p5) ∧ ((p4 ∨ (((p2 → p3) → ((False ∨ False) → (p2 ∧ True))) ∨ (p4 → p3))) → (p2 ∨ (p3 ∨ ((p5 → p2) ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197788732775352734128300302115 : ((((p5 ∧ p2) ∧ True) ∨ (p1 ∨ (p3 ∨ p1))) ∨ (((True ∨ p1) ∧ ((p2 ∧ p1) ∧ (p3 → p1))) → (((p5 ∨ (True ∨ p1)) ∨ p2) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172711138943975928573238753169 : (((p2 ∨ p5) ∨ (((p5 ∧ ((p5 → (p3 ∧ (True → p2))) ∨ False)) → p5) → p2)) ∨ (((p2 ∨ p5) ∧ True) ∨ (((p1 ∧ True) ∨ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232332219117802341705882370316 : (((p4 → True) → False) → (((((((False ∨ p4) ∨ False) → p2) ∧ (p4 ∨ p3)) ∧ ((p1 ∨ ((p4 ∨ p3) → True)) → p2)) ∧ (False → p3)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65100812123736068036326727715 : ((p2 ∨ (p3 ∨ (((True → p3) ∧ ((p2 ∨ p2) → (p5 ∧ (p4 ∨ (p1 → (((p4 → p2) ∧ (p1 → (p1 ∨ p5))) ∨ p4)))))) ∨ True))) ∨ p5) := by
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
theorem thm_5_vars_264075389140562434618847056729 : (True ∧ (((True ∧ p1) ∨ ((False ∨ (False ∨ (p2 → p2))) → p2)) ∨ ((p3 ∧ (False ∨ ((p1 ∨ p2) → ((False ∧ (p3 → p3)) ∨ p4)))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156948859758468480667203844909 : (((((p3 → True) → (p2 → (p1 ∧ ((p4 ∧ p3) ∨ ((p1 ∨ p3) ∧ p1))))) → (p1 ∨ p5)) ∨ True) ∨ (p5 → (p2 ∧ ((p5 → p3) → p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42403837329185739366231055119 : (((p4 ∧ (True → (p3 → (((True ∧ p4) ∧ p5) ∧ (((p5 → (False → p2)) ∨ (True ∧ p3)) → ((p3 → p1) ∨ (False ∨ p3))))))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147508221213498044944786629366 : (((p2 ∨ ((p1 ∨ (p2 ∧ (p2 → (p3 ∧ (True ∧ p5))))) → ((((False → p2) ∨ False) ∧ False) ∨ p5))) ∨ p3) ∨ (p3 ∨ (p2 → (True → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139669959728902957566626162283 : (((((p5 ∧ True) ∨ p4) ∧ (p4 ∧ (p1 ∧ (p2 → (p1 → (((p5 → p1) ∨ (True ∧ (p2 ∨ p2))) → p3)))))) → True) → ((p3 ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37174714413062276455343426019 : ((((((p5 ∧ (True ∧ (p3 → (p4 ∧ False)))) ∧ (p3 → (p2 → p4))) ∧ (((p4 → p5) ∧ (p2 → p5)) → (p2 ∨ p1))) ∧ p5) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720794505323098315081026977104 : (((((p2 ∨ (p3 ∨ p2)) → p5) → ((True → p5) → (((((p1 ∨ (p2 ∧ p5)) ∨ p4) → ((True → p5) ∧ p2)) → (p5 → p3)) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193792102445893204841298827870 : ((p4 ∧ ((True → p3) → ((p1 ∧ (p5 ∧ p4)) ∧ p1))) → ((p4 ∧ p2) ∨ ((p3 ∨ (((p3 ∧ ((True ∧ p5) ∧ p4)) ∧ p4) → p3)) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750197510791835373397117532307 : (((True ∧ (((p5 ∧ (p1 → p2)) ∨ (((p1 ∨ (p2 ∨ p3)) ∨ p3) ∨ (p5 ∨ (((p2 ∧ (p3 → p5)) → p2) ∨ p1)))) ∧ (True ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126062937950159094616217656837 : (((p5 → p1) → ((((p3 ∧ (True ∧ p2)) → True) ∨ (p5 → ((False → ((p5 → p4) ∧ True)) ∨ ((p4 ∨ p4) → p5)))) ∨ p4)) → (p1 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190103538659227822940957669507 : (((((p2 → p4) ∧ (p2 ∨ p3)) → (False ∧ False)) ∧ p5) ∨ ((p4 ∧ False) → ((p1 ∧ (False → (True ∧ ((p1 ∨ True) ∨ (p2 → False))))) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724817286138329864646276461974 : ((((p4 ∨ (True ∨ p2)) ∧ (((p1 → p4) ∨ (((((p2 ∧ (p1 ∧ True)) → p4) ∧ p2) ∧ p2) ∨ (((p4 ∧ p3) → p1) ∨ True))) ∧ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340090534262091229400579230374 : (p1 → (p3 → (((p1 ∨ False) ∧ ((p5 ∧ ((p5 ∧ (p5 ∧ ((p4 → (((p3 ∧ p2) ∧ p5) ∨ p1)) ∨ (False → p4)))) → p4)) ∨ p4)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147140832965334662648126689021 : (((False ∧ (((((p3 ∨ p3) ∧ p4) ∨ p5) ∧ ((p4 ∧ p1) ∧ p5)) ∧ ((p1 ∧ True) ∧ (p4 ∨ p2)))) ∧ p2) ∨ ((p5 ∨ True) ∨ (p3 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633828872224101873699141682795 : (((((((False ∨ ((p5 ∨ (p3 ∨ (p3 → True))) ∧ (p5 → (p3 ∧ (p4 ∧ (p4 → False)))))) ∨ (p2 ∨ p2)) ∧ p3) → (p4 → p3)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147399241355095398286658686505 : ((((p4 ∨ (((True → p2) → True) ∧ False)) ∧ ((p1 ∧ ((True → True) ∧ True)) → (p4 ∧ (p4 ∧ True)))) ∨ p4) ∨ ((p5 ∨ p2) → (p2 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620167463384651350810133734711 : (((((p2 ∧ p2) ∨ ((((p5 ∨ (p5 → (((False ∧ ((True ∨ p5) ∨ (False → p1))) → p2) ∧ (p5 → p3)))) ∨ True) → False) ∧ p1)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7823879433522550957544903302 : (((((p2 ∨ (p1 ∨ (p5 ∨ p4))) → (True → (((p4 → (p2 ∧ (p1 ∧ (p1 ∧ (False ∨ p3))))) ∨ True) ∧ (False ∨ False)))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158767594027410714636571859876 : ((p4 ∧ (True ∧ (p5 ∧ ((True → (p3 ∨ p2)) ∨ ((p4 → p5) ∨ ((p1 → p5) ∧ (True → p2))))))) ∨ ((p4 ∧ p3) → (True ∨ (False → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722128971333733540652837927956 : ((((p3 → ((p2 ∧ p2) → p3)) → (((p4 ∨ True) ∧ ((p1 ∨ ((((p1 → p1) → False) → ((p3 → p1) ∨ False)) → p2)) ∨ p5)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48076645980780973226959477651 : ((((p4 → ((p5 → (p5 ∧ p5)) → p3)) ∧ ((p2 ∨ ((p2 ∧ (p4 ∨ p3)) → False)) → (((p3 ∨ p5) ∨ p5) ∧ True))) → (False ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338166607893142299691316954315 : (p1 → ((((True ∧ p2) ∨ p5) ∨ (p5 → (False ∨ p1))) → ((p3 ∧ (p3 → False)) ∨ ((p5 → (p3 → p4)) → (((p1 ∨ p3) ∧ True) ∨ p5))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180369348490278787937205415986 : ((((p2 → ((True → (p1 → p4)) ∧ (p5 ∧ False))) → True) ∨ (p3 ∧ p4)) → ((False ∨ (False → p1)) → ((((False ∨ p3) ∧ p5) ∧ p1) ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_24902868198765189659649232442 : ((((p1 ∨ p3) → p3) ∨ ((((((True → (p4 ∨ p5)) ∨ p1) → p5) ∨ True) → (False ∧ p5)) ∨ (False → (p1 ∧ ((True ∧ False) ∧ True))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41144724802548753719000970981 : ((((((p2 ∨ p3) ∧ (((p3 ∨ p3) ∨ p1) → p3)) ∧ (((True → False) ∨ (p2 → (False ∧ False))) → p3)) ∨ (p5 ∨ (p3 ∨ p5))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174717225426927684698891980072 : (((p4 → (p1 ∧ p4)) ∨ ((False ∧ ((p3 → ((p2 ∧ False) ∨ False)) ∧ p3)) ∨ p5)) → (((p5 → False) → (p1 ∨ p5)) ∨ ((False → p2) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598682170182664551549073679304 : (((((p2 → (p5 ∧ p4)) → (((((p5 ∧ False) → p5) → ((p4 ∨ p2) ∧ p5)) ∧ p2) ∧ (((False ∨ p2) ∨ True) ∨ (p5 → p5)))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171550656296610755255307085294 : (((((p2 → ((((p2 ∧ False) → True) → (p2 ∨ p3)) ∨ p3)) → p2) → p3) ∨ p3) ∨ (False → (((((p3 ∧ True) ∨ p4) ∧ True) → False) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h1
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798894204120591524930194295148 : (((p1 → ((p3 ∨ False) ∧ (((p5 → p5) ∧ (((((True ∨ False) ∨ (p1 ∧ (p5 ∧ p3))) ∨ p1) → ((p3 ∨ p4) ∨ True)) ∧ p2)) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313082536890542938081938684429 : (p3 ∨ ((((((True ∧ ((p2 ∨ (p3 → False)) ∧ ((False → True) ∨ (False → (p4 ∨ False))))) ∧ p5) → p4) ∧ (p3 ∨ False)) ∨ (p2 ∨ True)) ∨ False)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667402539664264756501577441692 : (((((True ∨ p2) → (((((p5 ∨ (p1 → (p3 ∨ p1))) ∨ (p5 ∧ p4)) ∨ ((p4 → False) → False)) → True) ∧ p4)) ∧ ((p1 ∨ p4) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727831576258800662439391252400 : ((((p1 ∨ (False ∨ p5)) ∨ ((p3 ∨ (((True ∧ (p2 ∨ p4)) ∨ p5) ∨ (True ∨ p5))) ∨ (True ∧ (p3 → ((p4 ∨ p1) → (p4 ∨ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



