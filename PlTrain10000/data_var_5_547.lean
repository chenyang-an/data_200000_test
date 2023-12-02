variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136600204069337192026178431694 : (((p5 ∨ (p1 ∨ False)) ∨ (((False ∧ (p4 → p2)) ∧ ((False → True) → (p3 ∨ True))) ∨ ((p2 → True) ∧ (p3 ∨ False)))) ∨ (False → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148208570789098280227524047020 : (((p2 ∨ ((False ∧ p5) ∨ (True ∨ (p2 → ((((p3 ∧ False) ∨ p5) → p5) ∨ False))))) ∧ ((False ∨ p4) ∧ p1)) ∨ (p2 ∨ (p2 → (p2 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698400300910104321567652084541 : (((((p1 ∧ (((False → p4) → (p2 → p3)) ∨ p1)) → (False ∨ p2)) ∨ ((False → (True → (False ∧ (p1 → p2)))) ∨ ((p3 ∧ p3) ∧ p2))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144520248902903709265730417924 : ((((p1 ∨ (((p3 → (False ∨ True)) ∧ ((True → p3) → ((False ∧ p3) → p2))) ∧ p1)) ∨ p4) ∨ (p4 ∨ True)) ∧ ((False → (p1 → False)) ∨ p1)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114118611342678118555801378394 : (((p5 ∨ ((p5 ∧ True) → ((False ∨ p5) → (p4 ∨ ((((p2 ∧ (p4 → False)) ∨ False) → p4) ∧ True))))) ∨ (p3 ∨ (p2 → False))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760090372890931861683627480142 : (((p2 ∧ (((p4 ∧ p3) ∨ False) ∨ (p2 ∧ ((False ∨ p5) ∨ (p3 → ((((((p1 ∧ (p4 ∧ p4)) ∨ p2) ∨ False) ∨ p3) ∧ p2) → p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184487107552406547648005322980 : ((((((True ∧ p3) ∨ p4) ∧ p4) ∧ (p5 ∧ p3)) ∨ (p2 ∨ p2)) ∨ ((False → p4) ∨ ((((p3 → True) → p5) ∧ (False → p1)) → (True ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737674752778367108864367654369 : ((((p5 → p4) ∧ (((p1 ∧ p4) ∨ ((((p2 ∧ (((True ∧ True) ∧ (False ∨ (p3 ∧ p2))) ∧ (p5 ∧ p2))) ∧ p1) ∧ p3) ∨ p1)) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53207232064964898931351883938 : ((((p5 → (False ∨ ((p3 ∨ (p2 ∨ True)) ∨ p5))) → (p3 ∧ p5)) ∨ (p3 ∨ (p1 → ((((p3 ∧ p5) ∧ False) ∧ (p3 → p1)) → p2)))) ∨ p3) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104585911626057100697613532131 : (((((p1 ∧ (p5 ∨ ((p3 ∨ p5) ∨ p5))) ∨ ((False → p4) ∨ False)) ∨ ((p1 → False) ∧ ((False → False) → p1))) ∨ (p5 ∧ p1)) ∧ (p5 → p5)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89361066561424276857476615851 : (((True → (p3 ∧ p4)) ∧ ((((((((False ∨ p5) ∧ ((p4 → False) ∨ p3)) ∧ False) → p3) ∧ ((p2 ∧ p5) ∧ p1)) → p5) ∨ True) ∨ p1)) → p4) := by
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
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- We need to get the right conjuct of h7 based on <expert-advice>.
      let h8 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137777197584423367949290371677 : ((p2 ∨ (((p2 → ((p3 ∧ p3) → p5)) → p5) ∧ ((p5 ∨ p3) → (p1 ∧ ((p1 ∨ p2) → ((p2 ∧ True) ∨ False)))))) ∨ ((False ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789320267949210518130626829330 : (((p5 ∨ (((False ∨ ((((p4 ∨ True) ∨ (p5 → (p5 ∧ p5))) → p1) ∨ (p2 ∨ p5))) ∨ p4) ∨ (p5 ∨ (p5 → (p2 ∨ (p2 ∨ p5)))))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38287921390426414997269235725 : (((((p2 → p3) → ((True ∧ (((p4 ∧ p4) ∧ (p1 ∨ (p2 ∧ (p5 ∨ p2)))) ∧ p2)) → p1)) ∨ (((False → p1) ∧ False) ∧ p2)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1790042383333771593647946778 : (((((p5 ∧ p5) → p1) ∨ (p4 → (p1 ∨ (p5 ∧ True)))) → (True ∧ ((p1 ∧ ((p4 ∧ p3) ∧ p2)) ∨ p1))) ∨ (False → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61563720760820427984540235306 : ((p1 ∧ ((False ∧ ((p3 ∨ False) → (p4 ∧ p4))) ∧ (p5 ∨ ((p1 ∨ ((p4 ∧ (p2 ∧ p2)) ∨ False)) → (p3 ∨ (False ∨ (True → False))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53108109210069301582459175260 : (((False → ((False → p3) ∨ (((p2 ∨ p3) → (p2 ∨ p5)) ∨ p1))) ∧ (False ∨ ((True ∧ (p1 → (True → p5))) → ((p5 ∧ p5) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194081586094047749414149016099 : ((True → ((p5 ∨ p2) ∧ (((p2 ∨ p2) ∨ p3) → p4))) → ((p4 ∨ p2) → (((((p3 ∧ p4) → (p1 ∧ p4)) ∨ False) ∨ (p4 → True)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
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
theorem thm_5_vars_184248382397578245991161428266 : ((((p2 ∧ ((((False ∨ p2) → p5) ∧ True) ∧ False)) → p5) → p4) ∨ ((((p5 ∨ p1) → p4) ∨ ((p2 → p1) ∨ ((p4 → p3) ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590648100762828225099970951873 : (((((p3 ∧ ((((p1 ∧ p3) → p1) → (p3 ∧ p1)) → ((p3 ∨ False) → (p1 ∨ ((False → (p4 → (p2 ∨ False))) ∨ p3))))) → p2) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781135503312287118244824798916 : (((p2 ∨ ((p1 → False) ∨ (False ∧ (p3 → (p5 ∨ ((False ∨ (((p5 ∧ p3) ∨ p4) → ((((p3 ∧ True) ∨ p5) ∧ p1) ∧ p5))) ∨ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50168698141556608900743914863 : (((p5 → (p5 → (p4 ∧ (((((p4 ∨ (False ∧ (False → p2))) → p2) ∧ False) ∧ (p4 ∨ p1)) ∨ False)))) ∧ ((p2 ∨ p2) ∨ (p2 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191487985416457874616244292768 : ((True ∧ (True ∧ ((True → ((p3 ∨ p4) ∨ p3)) ∧ p5))) ∨ (p3 ∨ ((p4 ∨ (p1 → (((p2 → p5) ∨ p4) → p4))) ∨ ((p2 ∧ False) → p2)))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645437469709019398508167764344 : ((((p4 ∨ (((p4 → (((p4 → p3) ∨ True) ∧ p1)) ∨ p4) ∧ (((p3 ∨ p4) → (((p3 → p2) → (p1 → p1)) ∧ p1)) → p3))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136885588318717682693458962263 : (((p2 ∨ p3) ∨ ((((p5 ∧ p5) ∨ p5) → False) ∨ (p3 ∧ (p4 ∨ ((p1 ∨ p1) → ((True → p2) ∨ (p3 ∨ p2))))))) ∨ ((p5 ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356519729443866512385633178520 : (p5 → ((((True ∧ p5) ∧ ((p4 ∨ (p2 ∨ p2)) ∨ p2)) ∧ p2) ∨ (True → (True ∨ ((((p3 → p1) → p1) ∨ True) → (True → (p2 ∧ False))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114444450274387355090958689775 : (((p2 → ((((((True → p3) ∨ p3) → (p2 → (p4 ∧ (p2 ∧ False)))) ∨ p2) → p3) → p3)) ∨ (((p3 → True) ∨ p2) ∧ p1)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210772596236494494194290258736 : (((False ∧ (p1 → True)) → False) ∧ ((p4 ∧ (((p5 ∧ p3) ∧ p2) ∨ ((p4 ∨ (p1 → p4)) ∨ p5))) ∨ ((p5 ∨ (False → (p3 ∧ True))) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252528174463519570272901314099 : ((p5 → p2) ∨ (((p3 ∨ (((p5 ∧ ((p1 ∨ (p1 ∧ (p2 ∧ p1))) → p5)) → p1) ∨ p1)) ∧ p3) ∨ (p2 → (p2 → (False → (True ∨ False)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148972785028501301613482658723 : ((((p5 ∨ p4) → p4) ∧ ((((((p2 ∧ False) ∧ (p5 ∨ False)) ∧ p1) ∨ ((p3 → p2) ∨ True)) ∧ p4) ∨ p1)) ∨ ((p3 ∧ (p1 ∨ p3)) → p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166918073215892191940708849400 : (((((False ∧ p5) ∧ (p3 ∧ p1)) ∨ (((True ∨ p5) ∧ (p2 ∨ (p2 ∨ False))) → p2)) ∧ p1) → (((True → (p4 ∧ p3)) ∨ True) ∨ (p2 ∧ p1))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706383629844056015836628598332 : ((((False ∨ ((False ∨ (p1 ∧ p1)) ∨ (p5 ∧ False))) ∧ (p1 → ((p1 ∨ (((p1 → p5) → (p5 ∨ (p1 → (p4 → p5)))) ∧ p4)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805431870538974890855550482373 : (((p3 → (p2 ∨ (((False ∧ (p2 → (p3 ∧ p4))) ∨ (p3 → (p4 ∨ ((p1 → ((p5 ∨ ((p4 → True) → True)) ∨ False)) ∨ p2)))) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60070230559181752748148952355 : (((p2 ∨ p3) → ((((p5 → True) → (((((p4 ∨ p2) ∧ True) ∧ p2) ∨ ((p4 ∧ p2) → p1)) ∧ p5)) ∨ (p3 → (p5 ∨ p1))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164921794278583489990529981198 : (((((((((p1 → (p3 ∧ True)) → p4) ∧ False) ∨ (p1 ∧ False)) ∧ False) → p3) ∨ False) → p2) ∨ (((p5 → (p1 → p3)) → True) ∨ (p1 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254452585041639918048066406380 : ((p3 ∧ True) → (((False ∧ ((p5 ∧ (p4 → (p2 ∧ (p3 ∧ ((((p2 → p3) ∨ p1) → p5) ∨ p1))))) ∧ p4)) ∨ ((p3 → p1) → p3)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178222198605678176074062784952 : (((False → ((((p5 ∧ p1) ∨ p1) ∨ False) ∧ (p1 ∧ (True ∨ True)))) → p5) ∨ (True → (((p3 → (p2 ∨ p5)) → (True ∨ p5)) → (p5 ∨ True)))) := by
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
theorem thm_5_vars_113062389701180487313709980590 : (((p2 ∨ (True ∧ (((p3 → (((p1 → p4) ∨ p4) ∧ p4)) → True) → (True → (p3 ∧ (((p4 ∨ p2) → p5) ∨ False)))))) → p1) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231940022799405687732941335509 : (((p1 ∨ True) → p1) → (p4 ∨ (False ∨ (((p1 → (((p1 → p2) ∨ p3) ∨ False)) ∧ False) ∨ (((((p2 ∨ False) → True) ∧ True) ∨ p3) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54487030699716083491893219747 : (((((True → (p3 ∨ p4)) ∨ p5) → (p3 ∧ p5)) ∨ (False → ((p5 → p2) → (((p3 ∧ (p4 ∨ ((True ∨ False) ∨ p4))) → p5) → False)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47228302658831710307635645769 : ((((p2 ∨ ((p2 ∨ (p3 ∨ (p4 → True))) ∧ True)) ∧ ((p1 ∧ (p2 ∨ False)) ∨ (p4 → ((p4 → (p5 → True)) ∨ False)))) ∨ (p1 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669272332691095483321570374944 : (((((p1 → ((True ∨ True) ∨ (False → (((p3 ∨ p3) ∨ ((p4 → p2) ∧ p1)) → ((p5 → p2) ∧ p4))))) → p4) ∨ ((p5 ∨ True) ∨ False)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_65766685655462615025438069484 : ((p4 ∨ (((True → (p1 ∧ True)) → (((((False → (p1 ∧ p5)) → p2) ∨ p1) → p5) ∨ True)) ∧ ((p2 ∨ (True → p4)) ∨ (p4 → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183873708364131140027185617882 : (((((p4 → p4) ∧ True) ∧ ((p4 ∧ p1) ∨ (p4 ∧ p3))) ∧ p4) ∨ ((((p3 ∧ True) ∨ p2) ∨ (True ∨ ((False ∧ p5) ∧ (p4 ∧ p4)))) ∨ False)) := by
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
theorem thm_5_vars_42569977794180812801868137116 : (((p2 ∨ ((((p4 ∧ (False → p3)) ∨ ((False → p2) → p1)) ∧ ((p3 ∧ ((True → ((p2 ∨ False) ∨ p1)) ∧ p1)) → p5)) ∨ p5)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139709611047011500858365531882 : ((((p3 ∨ p5) ∨ (p1 ∨ ((((p5 ∧ p1) ∨ ((((p4 ∨ p3) → False) ∧ p4) ∧ p5)) ∧ p4) → (p5 ∧ p4)))) → False) → ((p2 ∧ p4) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ p5) ∨ (p1 ∨ ((((p5 ∧ p1) ∨ ((((p4 ∨ p3) → False) ∧ p4) ∧ p5)) ∧ p4) → (p5 ∧ p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h11
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h20.left
      let h23 := h20.right
      -- One of the premise coincides with the conclusion.
      exact h15
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h24 := h1 h2
  -- False on the left can always be used.
  apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_467804630167183926814729478366 : ((((((p1 ∧ p4) → p3) → ((True ∨ p1) ∧ (False ∨ (True ∧ (True → p4))))) ∨ (((False → (p5 ∧ ((p2 → p3) ∧ p4))) ∨ p5) ∨ p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355633656877171297916772932882 : (p5 → ((True → (((p4 ∧ ((False ∧ p3) → p5)) → ((False ∧ (((p3 → p4) ∨ True) → p2)) ∧ p2)) ∨ (p3 → (p5 → p3)))) ∨ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350102320202787318557447499233 : (p4 → ((((p2 → p2) ∧ (True ∨ ((p1 ∧ ((p1 ∨ ((True ∨ p3) → p1)) ∨ (False ∨ p2))) ∨ (True → p1)))) → ((p3 ∨ p3) ∧ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234013683057274546946306299603 : ((p5 ∨ (p4 ∨ False)) → ((((False ∨ ((((False ∧ p3) → (p5 ∨ (((p2 → p2) → p2) ∨ p4))) ∨ p5) → p5)) ∨ True) ∨ False) ∨ (p5 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613934801428912278020605756822 : (((((((((p1 ∧ False) → p2) ∨ (p5 → (p4 → p1))) → (p5 ∨ ((True ∨ p5) → True))) → (False ∧ p1)) ∨ (False → (p1 ∨ p2))) ∨ p1) ∨ p3) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312984365465715461879818433305 : (p3 ∨ (((p2 ∨ (p5 → ((p1 ∨ (((p2 ∧ (((True ∧ p5) → p5) ∨ False)) ∨ p2) ∨ (p1 ∧ p1))) ∨ ((p4 ∧ True) ∧ False)))) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621321811003540845063022519453 : ((((True ∧ (((p4 → False) ∧ (p3 ∧ p2)) → ((p4 ∨ p5) ∧ (((((p5 ∧ p3) ∨ ((False → p4) → p2)) → p1) → p2) → p1)))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_676524825927911034199095655363 : ((((False ∧ ((((((p4 ∨ (p4 ∧ (False → (p5 ∨ p4)))) ∧ (p3 ∨ p5)) ∨ p5) ∧ p3) ∨ p5) ∨ p2)) ∧ ((True → p3) ∧ (p1 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696554063943910360707908098752 : ((((((((p4 ∨ p5) ∧ False) ∨ ((p4 → p2) ∧ p1)) ∧ p4) ∨ p4) ∧ (False → ((p1 ∧ p3) → (p3 ∨ (p2 → ((p3 ∧ p1) ∨ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315718717706476311043532310077 : (p3 ∨ ((True → p3) ∨ ((((p5 → p4) ∧ ((p4 → ((p4 ∧ ((p1 → False) ∨ (p1 → ((p5 ∨ p4) ∧ p5)))) ∧ p3)) ∧ p4)) ∧ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317783211023768649291965471366 : (p4 ∨ (((((((p2 ∨ (p1 ∨ False)) ∨ p1) → (p1 ∧ p2)) ∨ p5) ∨ p2) → (False ∨ ((False ∨ (p3 ∨ ((p3 ∧ True) ∨ p3))) → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178792841289562964049794316170 : ((((p4 ∨ p3) ∧ p4) ∨ (p4 ∧ ((p4 → (p4 → True)) → (p1 → True)))) ∨ (True ∧ (False ∨ (((p4 → (True ∨ (p1 ∧ p4))) ∧ True) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198217235559935474822804822958 : ((True ∧ (((False ∨ p3) → (False ∧ False)) ∧ p5)) ∨ ((((((False ∨ p5) ∧ p1) ∧ ((p5 ∧ (p1 ∨ p1)) → True)) → (p4 ∧ p4)) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249556811373864052865820887880 : ((p5 ∨ p2) ∨ ((p4 ∧ ((p1 → ((p4 ∧ (p2 ∨ p1)) ∨ True)) ∨ False)) ∨ (((False ∧ p1) ∧ ((False ∨ (False ∨ False)) → p3)) → (False ∨ p5)))) := by
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135841502527593874690658424241 : (((p3 ∧ (((p2 → (((False ∨ p3) → p5) ∨ p2)) → p1) ∨ True)) ∧ ((p3 → (p2 → False)) ∧ ((p5 → False) ∧ p3))) ∨ ((p5 ∧ p2) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164525338082306475732351623713 : (((((p1 → p5) → (p5 ∨ ((((True ∧ True) → p4) ∨ p4) → p2))) → (p2 → p4)) ∧ True) ∨ (p3 → ((p3 → ((p1 → p3) ∧ p5)) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191738598649977622013402833294 : ((False ∨ (((p2 ∧ p1) ∧ (p4 ∨ p3)) ∨ (True → False))) ∨ (False ∨ ((p3 → ((True ∨ (p5 ∧ (p3 → p2))) ∨ (False ∧ False))) ∨ (p4 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111390045346373639120070410596 : (((False ∨ (p5 → (((((p5 ∧ p3) ∨ ((p4 ∧ ((p5 ∧ p4) ∨ True)) ∧ p5)) ∨ (True → p1)) ∧ (p4 → p4)) ∧ p5))) ∧ p4) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115295672466641056548839701425 : ((((((True ∨ p2) ∨ p1) → ((p1 ∨ p4) ∧ p3)) ∨ p3) → ((p2 ∨ ((p2 ∨ p3) ∨ (((p5 → True) ∨ False) ∨ p1))) → p1)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750779564607591207704852404099 : (((True ∧ (((p4 → (p4 ∨ (False → p1))) ∧ (p3 ∨ ((False ∧ p3) ∨ p3))) ∨ ((False ∨ True) → (p3 ∨ ((p5 ∧ (p1 ∧ p3)) → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172368212623224236577812436969 : (((False ∧ ((False → (p3 → p5)) → False)) ∨ (True ∧ ((p5 ∧ (p3 ∧ p4)) ∧ p5))) ∨ (False → (True ∧ (p2 ∨ ((p2 → (p4 → True)) → False))))) := by
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
theorem thm_5_vars_747738816605403731642679923456 : ((((False → False) → (False ∧ (True ∧ (p1 ∧ ((p3 ∨ (p5 → ((p5 ∧ p1) ∧ (False ∧ p5)))) → (p4 ∧ (True ∨ (p2 ∧ (p2 ∧ False))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206308291003142556292414979758 : ((p1 ∨ ((p2 ∨ False) ∧ (p4 ∧ p2))) ∨ (p2 ∨ (p2 → ((p1 → ((((((p4 → True) ∧ p4) ∧ p2) ∨ p1) ∨ p3) ∧ p3)) → (p3 → p2))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56332357883244909076035516413 : (((((p4 ∨ p1) ∧ p4) ∨ p1) → ((True ∧ ((((p2 → ((((True ∨ p4) ∧ p5) ∨ p1) ∧ p3)) ∨ p2) ∨ p1) → (p3 ∧ True))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262214386572133264885599223016 : (True ∧ (((p5 → ((p5 ∧ (p4 ∨ (p5 ∨ ((((((p1 ∧ False) ∨ p2) ∨ False) ∨ p4) ∧ p1) ∧ (p3 ∧ (p4 → p2)))))) ∨ False)) → p4) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134263598230238447469304219551 : (((((True → p4) → p2) → ((True ∨ (p4 → False)) → (False ∧ (p5 → (((p1 ∧ p5) ∧ (p4 → p3)) ∨ p3))))) ∨ True) ∨ ((p2 → p1) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348990095143411671507436520593 : (p3 → (p4 ∨ ((p4 ∨ ((((p2 ∨ False) ∨ (True ∧ p2)) ∧ (p2 ∧ ((p2 ∨ p2) ∨ True))) ∨ p3)) ∨ ((True ∧ False) ∨ ((p1 ∨ True) → True))))) := by
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
theorem thm_5_vars_111245789442168114175155313789 : ((((p4 → p2) ∧ (((p2 ∨ ((True ∧ ((p5 ∧ p1) ∨ (p2 ∧ ((p4 → p2) ∧ (p1 → p3))))) ∨ p2)) ∧ p1) → False)) ∧ p3) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313031189813861996940278323127 : (p3 ∨ (((((p2 ∨ (p1 ∨ p2)) ∧ ((p1 → (False ∨ ((False ∨ p3) ∨ ((True ∨ p4) → ((p3 ∧ False) → False))))) → False)) ∧ p2) → p4) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h4
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (p1 → (False ∨ ((False ∨ p3) ∨ ((True ∨ p4) → ((p3 ∧ False) → False))))) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h12
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h7
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h16 : (p1 → (False ∨ ((False ∨ p3) ∨ ((True ∨ p4) → ((p3 ∧ False) → False))))) := by
        -- Implications on the right can always be decomposed.
        intro h17
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Implications on the right can always be decomposed.
        intro h19
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- False on the left can always be used.
        apply False.elim h21
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h22 := h5 h16
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h24 : (p1 → (False ∨ ((False ∨ p3) ∨ ((True ∨ p4) → ((p3 ∧ False) → False))))) := by
        -- Implications on the right can always be decomposed.
        intro h25
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h26
        -- Implications on the right can always be decomposed.
        intro h27
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- False on the left can always be used.
        apply False.elim h29
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h30 := h5 h24
      -- False on the left can always be used.
      apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309339527067819428760251578284 : (p2 ∨ (((True → (((((((p1 ∨ p2) ∨ True) → p5) → p5) → (p5 → p2)) → (p4 ∨ p2)) ∧ True)) ∧ (p3 ∨ (p1 ∧ p5))) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51091610486230974286895649661 : (((((p5 ∨ (False ∨ (p5 ∧ (p1 → ((p3 ∨ (p4 ∧ (True ∧ p2))) ∨ True))))) → p2) ∧ False) ∨ (p3 → (p1 ∧ ((p2 ∨ p1) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720865574713626225908853622185 : (((((p5 → (p5 ∧ p5)) → p2) → ((((((False ∧ p5) → (((p2 ∨ p2) ∧ p5) ∨ (p3 → p4))) → p4) → False) ∧ (p2 → p1)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148840147725687108960973522001 : (((((False ∧ False) ∧ p5) → p5) ∧ ((((p1 ∧ (p1 ∨ p5)) ∨ (True ∧ p2)) ∧ p5) ∨ (True ∨ (False ∨ p4)))) ∨ (True ∧ ((p1 ∧ False) ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117291688886487243473943966837 : ((False ∧ ((p1 ∧ ((((p3 ∨ p1) ∨ (((((True → (p2 ∨ p5)) → p2) → True) ∨ p5) ∧ p5)) ∧ p1) ∧ (True → p1))) → p2)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350086975847086477827088365678 : (p4 → ((((((((p3 ∨ ((((p5 ∧ False) → False) ∨ p4) ∧ True)) ∨ (p2 ∧ p4)) ∧ p1) ∨ True) ∧ True) → p2) ∧ ((True ∨ True) ∨ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113604132804431734351013144438 : (((p1 ∨ (p2 → ((True ∨ True) ∧ (((p3 → p4) → (((p3 → True) ∧ p1) ∧ p3)) ∨ ((p2 ∧ p2) ∨ p1))))) ∨ (p5 → False)) ∨ (p3 → False)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245508779103654319321013890266 : ((p2 ∧ p5) ∨ (p2 ∨ ((((((p3 → (True → (True → False))) ∧ (((p3 ∨ p2) ∧ p1) ∨ ((p3 ∧ p4) ∨ False))) ∨ p2) ∨ True) ∨ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135218870190739310656286003726 : (((((p3 → (p5 ∨ (False ∧ p5))) → ((True ∧ (p4 ∧ p3)) → p2)) → (False ∨ ((True ∧ p2) ∨ p3))) → (p1 ∧ p4)) ∨ ((False ∧ p2) → p5)) := by
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
theorem thm_5_vars_58274976774805939433382251448 : (((p5 ∧ p5) ∧ (p3 ∨ ((((p2 → (True ∨ (p1 → p1))) ∧ (((p1 → p2) ∧ (p4 → (False ∨ (True → False)))) ∨ p5)) ∧ p1) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134935693585305444786194381295 : ((((p4 → (((p3 ∧ (p1 ∨ True)) → ((p3 ∧ p4) ∨ ((p4 ∨ False) ∨ (p2 → p2)))) ∧ p4)) → p3) ∧ (p2 → p3)) ∨ ((p2 → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165916262624172171002901185673 : (((True ∧ p5) ∧ (p5 ∧ ((False ∧ ((((p2 ∨ p4) → p2) ∧ (p3 ∨ True)) → p5)) ∧ p2))) ∨ (((True ∨ p4) ∧ ((True ∨ p2) ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667253679583808108171952097491 : (((((p5 ∨ p3) ∧ ((((p5 ∨ p5) → (False ∧ ((False ∨ (p4 ∧ p4)) ∨ (p4 → (p3 → p1))))) ∨ False) ∨ p1)) ∧ ((p3 → p2) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167431156828117728228790209011 : (((p5 ∧ ((True ∨ p3) ∧ (p1 ∧ ((p5 ∨ p4) → (p4 ∨ ((p5 ∨ False) → p5)))))) → p3) → (p1 ∨ (False ∨ (p5 ∨ ((False ∧ p2) ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171571928508902035366126171615 : ((((((True → (p4 ∨ (p2 ∧ (p1 ∨ True)))) ∨ p1) ∧ p3) ∨ (p4 → p4)) ∨ True) ∨ (p4 ∨ ((p4 → p2) ∧ (p4 ∨ (p3 → (False → p2)))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166805390170048388675895591913 : (((((((True → (p2 ∨ False)) ∨ p1) ∨ p3) ∧ (p4 ∧ (p4 ∧ (p5 → p2)))) ∧ p5) ∧ p4) → (((((True ∧ p1) → True) → p2) ∨ False) ∨ p5)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h7.left
      let h11 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h7.left
      let h16 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h7.left
    let h21 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113034446123294361886933567060 : (((False ∨ (((((False ∨ ((p2 → False) → (p4 ∨ (p1 ∨ False)))) → ((p5 → (p2 ∧ p5)) ∧ p1)) ∧ True) ∧ p3) → p5)) → p2) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57924352841356749929609086928 : (((True → (p1 ∧ p2)) → (((((p5 ∨ (False ∨ p4)) ∨ ((p5 ∨ p5) ∨ p1)) ∨ p3) ∨ p4) ∨ ((p5 → p2) ∨ ((p4 ∧ False) ∨ p3)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65924922528733134192135861135 : ((p4 ∨ (p5 ∧ ((((True → (p1 → (p5 ∨ p2))) → p4) ∧ False) ∧ ((p5 ∨ (p4 → p1)) → ((((False ∧ p5) ∨ p2) ∨ p1) ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48090996038788849068507560500 : ((((False → ((p3 ∨ p1) ∧ (p5 ∧ p1))) → (((p1 ∨ ((p2 ∧ False) ∧ p1)) → ((p2 ∧ (p4 ∧ True)) → p2)) ∨ p3)) → (p5 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41235387737111512520810108525 : ((((p5 ∧ ((((((True → p5) ∧ (p5 → (p4 ∧ p3))) ∧ False) ∧ True) ∨ p3) ∨ (p4 ∨ p4))) ∧ (p3 ∨ ((p2 ∧ p1) ∨ p3))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697277240190972592659054479058 : (((((p3 ∨ p2) ∧ (p1 → (p1 ∨ (False ∨ (p5 ∧ (p4 → p2)))))) ∧ (p1 ∧ (((p1 ∨ (p4 ∨ (p2 ∧ p3))) ∧ p3) → (p3 ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191338334127538121471182707788 : (((p5 ∧ p2) ∨ ((p5 → False) → ((p1 ∨ p3) ∧ True))) ∨ (p5 → ((p3 ∨ p5) ∨ (p2 ∨ ((((p2 ∧ p2) → False) ∨ p1) → (False → False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707234167661475348634178345879 : (((((((p5 ∧ p2) → p2) ∧ True) ∧ (p5 ∧ False)) ∨ (p3 → (p4 → ((((p2 ∨ p4) ∨ ((p4 → (p1 ∧ p2)) → p5)) ∧ p5) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46942172244319066918468501875 : ((((p1 ∨ ((((p2 ∧ p3) → (p1 ∨ p5)) → p5) ∨ (True ∧ (p2 ∧ (p1 ∨ (False ∨ (p5 → (True ∧ p4)))))))) ∨ p4) ∨ (False → p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



