variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647416018251195067295054565743 : ((((p4 → ((True ∧ p2) → (p4 ∧ ((((False ∨ ((p2 → p1) ∨ (p4 → p1))) ∨ (p1 ∨ p3)) ∧ (False ∧ (p5 ∨ p2))) → True)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603193824804706148883117375267 : ((((p2 ∨ (((True ∨ (((True ∨ p4) → True) → p5)) → ((False → (p3 ∨ (p5 ∨ p1))) ∧ (p2 ∧ p4))) → ((p4 ∧ True) ∨ p5))) ∧ True) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (((True ∨ p4) → True) → p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702670028297888646197829809021 : ((((((p3 ∨ p3) → (True → (True → p4))) ∧ (p4 ∨ p5)) ∨ (p2 → ((p2 → (p4 ∨ (((p4 ∧ (p3 → p4)) → False) ∧ p4))) ∨ p2))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255253239672343606813533251005 : ((p4 ∧ p5) → ((((p4 ∨ (p2 ∧ p4)) → ((p3 ∨ (False → (((p1 → p3) ∨ p2) ∧ p5))) ∧ (p1 ∧ False))) ∨ (False ∧ p1)) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197841687245203213967380147886 : (((p2 ∨ (p3 → p5)) ∨ ((p5 → p1) ∨ p1)) ∨ ((p2 → (p3 ∧ ((p3 ∧ (p3 → ((p5 → p2) → (False ∨ (True ∧ True))))) ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259347122012488539867321113427 : ((False → p2) → (True ∧ ((((((((((p4 → p5) ∧ False) → True) → ((p1 → p4) ∨ False)) ∨ p3) → False) ∨ (p1 ∨ p2)) → p4) → p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149061989231983407899755439473 : ((((p3 ∨ p3) ∧ True) → ((True ∨ p4) → (p3 → (((((p2 ∨ False) → True) ∨ p2) → p2) → (p5 ∨ p2))))) ∨ (((p1 ∨ True) ∨ p4) ∨ False)) := by
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
theorem thm_5_vars_354585762685279757186778408533 : (p5 → ((((False → p4) → (((((p3 → (p3 ∨ (p2 ∨ False))) ∨ p5) → (p2 ∧ (p3 ∧ (True → False)))) ∧ p2) ∨ (False ∨ p5))) ∧ p5) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215367025290244580689950701885 : ((p2 ∧ ((p5 ∨ False) ∨ p4)) ∨ (((p4 ∨ ((p1 ∧ p1) → ((p5 ∧ (p4 → (True → (p2 ∨ True)))) ∨ (False → p1)))) ∨ p5) ∧ (False → False))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185625391728045849768818382926 : ((True → ((True ∨ p5) → (((p5 ∨ p1) ∧ (p4 ∨ p1)) ∨ True))) ∨ ((((p5 → ((True ∧ p4) → p3)) ∨ ((p5 ∧ True) ∧ p4)) ∨ p5) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_139224852413908523477243075443 : ((((True ∨ (p4 ∨ p5)) → ((((p3 ∧ (((p2 ∧ p3) → (p3 → p1)) ∨ True)) → p4) ∧ False) ∧ (p3 ∧ True))) ∨ p3) → ((p1 ∧ p5) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (True ∨ (p4 ∨ p5)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We need to get the left conjuct of h4 based on <expert-advice>.
    let h5 := h4.left
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760283748985645866162978952267 : (((p2 ∧ ((p2 ∨ p1) ∨ (False ∨ ((p4 ∨ (p2 ∧ (((p1 ∨ (p4 → (p2 → (False ∨ p4)))) ∧ p3) ∨ p1))) ∧ ((False → False) ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151843654060933279609454125559 : ((((True → ((((p4 ∧ p1) ∧ (p4 → (p3 → p4))) ∧ p4) ∧ True)) ∨ p2) ∨ ((False ∨ (True → p3)) ∧ p5)) → ((p3 ∨ p4) ∨ (p2 ∨ p2))) := by
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
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h4 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h5 := h3 h4
      -- We need to get the left conjuct of h5 based on <expert-advice>.
      let h6 := h5.left
      -- We need to get the right conjuct of h6 based on <expert-advice>.
      let h7 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h15 := h13 h14
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710098971869527357690078106531 : (((((p5 → (p5 ∨ (p1 ∧ p5))) ∧ p2) ∧ ((((p1 → p3) ∧ p2) ∧ (p3 ∨ (True → (p2 → (((p1 → p2) ∨ p3) → p5))))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48792830826014018446309590788 : (((False ∧ (((p3 ∧ (p2 → p3)) ∨ ((((p2 → ((p1 ∧ True) ∨ p5)) → p1) ∨ (True → False)) ∨ p1)) → p4)) ∧ (p1 → (p2 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621197896540032645494433581914 : ((((True ∧ (((((False ∨ (p5 → p2)) → (p4 ∨ True)) ∧ False) ∧ ((p4 ∧ p1) ∧ ((p1 ∨ (p2 ∨ (p4 ∧ p3))) ∨ False))) ∨ p3)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_216674134073533983497760063710 : ((((False → p3) ∨ p4) ∧ p3) → (True → (p5 ∨ (True ∧ (p2 ∨ (False ∨ (p4 → (p3 ∨ ((False ∧ True) ∨ (((p2 ∨ p2) → p5) ∧ True)))))))))) := by
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
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
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
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40422128941105020314438250395 : (((((False ∨ (((p4 ∧ (False → True)) ∨ ((True ∨ (False ∧ p5)) ∨ p1)) ∧ p5)) ∨ (p5 → (True ∧ (False ∧ (p1 ∧ p4))))) ∨ True) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187765983545295609257366837441 : ((p2 → (p3 ∧ (p4 ∧ (((p3 → False) ∨ (p4 ∧ p4)) ∨ p3)))) → (((p4 ∨ (p1 ∨ False)) → (p1 → p2)) → (p5 → ((True → p4) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111063935224762317723305929941 : ((((False → (((p3 ∧ True) ∨ ((p1 ∨ (p4 ∨ p4)) ∨ (p4 ∨ False))) ∨ True)) ∧ ((p3 ∧ False) ∧ (p1 ∨ (p2 ∨ p3)))) ∧ p1) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55907369707045532120326206815 : (((p4 ∨ (p4 → (p4 ∨ True))) ∧ (((((((True → p5) ∧ (p3 ∨ p1)) ∨ True) → p2) ∧ ((p1 ∨ p4) → (True ∨ False))) ∧ p2) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56646419061563132525408900880 : ((((p1 ∨ p2) ∧ p2) ∧ ((False ∧ False) ∧ (((p1 ∨ False) ∨ p2) ∧ (((True ∨ (p4 ∨ (False → True))) ∨ True) ∨ (p2 → (p1 ∧ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117592359004112692419576787151 : ((p2 ∧ (p5 ∧ (((((p5 ∨ False) → False) ∨ ((p4 ∧ True) ∧ (((p5 ∧ True) → (True ∧ p1)) → (True ∧ p4)))) ∨ False) → p4))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55877252918076203346220106038 : (((False ∨ ((p1 → p2) ∧ p5)) ∧ (((p4 ∨ p5) ∨ ((p3 ∨ ((p2 ∧ (p3 → p4)) → p3)) → p1)) ∧ ((p2 ∧ (False ∧ False)) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166195239035367187380414320484 : ((p1 ∧ (((p3 → (p5 → p2)) → (p4 ∧ False)) → ((False ∧ (p1 ∧ (True → p5))) → False))) ∨ (((False → True) → (False ∧ p3)) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171363369832986156201178709320 : (((((((p1 ∧ p5) ∨ (p1 ∨ p3)) ∧ (p1 ∨ p4)) → p3) ∨ (True ∧ True)) ∧ p5) ∨ ((True ∨ (True ∧ (p4 → p3))) ∨ ((True ∨ p3) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616730374729588460636295569345 : (((((((p1 ∧ (False ∨ (p2 ∧ p4))) ∨ p3) ∨ (p1 ∧ True)) ∨ ((p1 ∨ (p2 → p5)) → (((p1 ∨ p4) ∨ (p3 → p1)) → p3))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304683947064627024752917916254 : (p1 ∨ (((((((p1 ∧ ((p1 ∨ (p3 → p4)) ∨ p5)) ∧ p2) → (p3 → p2)) → (False ∧ ((p5 → True) ∨ p4))) ∧ p4) ∨ p3) ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227934179422266915719771588134 : ((p3 ∧ (p1 ∧ True)) ∨ ((p2 ∨ (p3 ∨ (((False ∨ ((False ∨ (p4 ∨ p3)) ∨ p3)) → p4) → ((p5 ∨ p4) ∧ (p4 ∧ (p5 ∧ p2)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58952076471963655607157901195 : (((p2 ∧ False) ∨ ((((((p1 → ((p5 ∨ p4) ∧ True)) → ((p1 ∧ (False ∨ False)) ∨ (p5 ∧ False))) ∨ p4) ∨ p1) ∧ p4) ∧ (p3 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725498202681862754007887479813 : (((((True ∧ p2) ∧ p4) ∨ ((p3 → (p5 ∧ (((p2 ∧ (p2 → p2)) ∧ p5) → True))) ∧ ((False → ((True ∧ True) ∨ (p4 → False))) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89156991323463370172455873401 : ((((False ∨ True) → p5) ∧ (((((p4 ∨ (p1 ∨ ((p1 → False) ∨ p3))) ∧ (False ∨ (p3 ∧ p1))) ∧ ((p5 ∨ False) → p3)) ∧ p5) → p4)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299358486869886351387115494124 : (False ∨ (((p5 ∧ p2) ∧ ((((p2 → (True ∨ p2)) ∨ False) ∧ p3) ∨ (((p1 → p4) ∧ (((p2 ∨ (p1 ∨ p5)) ∨ p4) ∨ p1)) ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56899789288975512430063824213 : (((p4 ∧ (p2 ∧ p1)) ∧ ((((True ∧ (True ∧ ((p3 → (p4 ∨ p2)) ∧ (p3 ∨ (p1 ∨ p5))))) ∨ p2) → ((p1 ∧ p3) → False)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55074863530373922598557517267 : (((p5 ∨ (False ∨ ((p5 → p3) ∧ p3))) ∧ ((((p3 ∧ p3) ∨ ((True → (((p4 ∨ True) ∧ p5) → p2)) → p3)) ∧ (p1 ∨ True)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186848148966613540169030603050 : (((p5 ∧ ((p5 → False) ∧ p5)) ∨ ((p5 ∧ True) ∧ (p1 ∧ True))) → ((p1 ∨ (p2 ∨ (p2 → p3))) → (p5 → (p1 ∨ ((p3 → p1) → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h12.left
      let h16 := h12.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
        have h24 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h23
        -- We have shown the premise of h22, we can now drive its conclusion.
        let h25 := h22 h24
        -- False on the left can always be used.
        apply False.elim h25
      case inr h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- Conjunctions on the left can always be decomposed.
        let h29 := h27.left
        let h30 := h27.right
        -- Conjunctions on the left can always be decomposed.
        let h31 := h28.left
        let h32 := h28.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h31
    case inr h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h34.left
        let h36 := h34.right
        -- Conjunctions on the left can always be decomposed.
        let h37 := h36.left
        let h38 := h36.right
        -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
        have h39 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h38
        -- We have shown the premise of h37, we can now drive its conclusion.
        let h40 := h37 h39
        -- False on the left can always be used.
        apply False.elim h40
      case inr h41 =>
        -- Conjunctions on the left can always be decomposed.
        let h42 := h41.left
        let h43 := h41.right
        -- Conjunctions on the left can always be decomposed.
        let h44 := h42.left
        let h45 := h42.right
        -- Conjunctions on the left can always be decomposed.
        let h46 := h43.left
        let h47 := h43.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h46



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149892610045610411716802236233 : ((p2 ∨ (True ∧ (p1 → (((((((p3 ∧ True) → (True ∧ p4)) ∨ p5) → (p2 ∨ p4)) ∨ p2) ∧ p1) ∨ p2)))) ∨ ((False ∧ True) → (p3 ∨ p5))) := by
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
theorem thm_5_vars_56854621850150433844875596284 : (((False ∧ (False ∧ False)) ∧ ((p2 → (p1 ∧ p3)) ∧ (((p1 ∧ p1) ∧ True) ∨ ((((p2 ∧ p2) ∧ p5) → (p1 ∧ p1)) → (p1 ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219761843842355202569116844348 : ((p2 → ((False ∨ True) ∨ p5)) → ((((p3 → p3) → p1) ∧ False) ∨ ((True ∧ ((p3 ∨ (p5 ∨ p1)) ∧ (p5 ∨ ((False ∧ p5) ∧ True)))) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- False on the left can always be used.
      apply False.elim h12
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Conjunctions on the left can always be decomposed.
        let h20 := h18.left
        let h21 := h18.right
        -- False on the left can always be used.
        apply False.elim h20
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h23 =>
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Conjunctions on the left can always be decomposed.
        let h27 := h25.left
        let h28 := h25.right
        -- False on the left can always be used.
        apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692129651746004584384619876410 : (((((p3 → ((False → ((False ∧ (p3 ∨ (p1 ∧ p4))) ∨ p4)) ∧ p4)) ∧ p5) ∧ (((((p5 ∨ p5) ∧ p1) ∧ (True → False)) ∧ p2) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149000676717467440541127811365 : (((p4 → (p4 ∧ p2)) ∧ ((p2 → (p3 → (((p3 → p5) → p2) ∧ (True → ((True ∨ False) ∧ p2))))) → False)) ∨ (p5 → ((True ∨ False) ∨ p5))) := by
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
theorem thm_5_vars_160390811412597439712330812016 : (((p5 ∨ (True → (p5 → ((((p1 ∨ p4) ∧ p5) → (False ∨ p3)) ∨ p3)))) ∧ ((p1 ∧ p3) ∨ p3)) → ((p4 ∧ ((p5 ∨ p2) ∧ True)) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
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
theorem thm_5_vars_46668961206086424429584490070 : (((p1 ∨ (((p1 ∧ ((((((p2 ∧ p4) ∨ True) → True) → p5) → p3) ∨ (p2 ∧ True))) ∧ (p4 ∧ (p1 ∨ p5))) ∨ True)) ∧ (False → p2)) ∨ p2) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317699707993598443002696144344 : (p4 ∨ (((p1 ∧ (p3 ∧ (p1 → ((p3 ∧ ((p1 ∨ ((p1 ∧ p3) → ((True → (p2 ∧ False)) ∨ p5))) ∧ p2)) ∧ False)))) ∧ (p4 → True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356353664007072882500018317639 : (p5 → (((p4 ∨ ((p3 ∨ p2) → (p4 ∧ (p1 ∧ p1)))) → (p4 → (p3 ∨ p3))) ∨ ((p5 → (p1 → (p4 → (p1 ∧ (p5 → True))))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250152219313722093484500410034 : ((True → p5) ∨ (((p4 → ((p4 ∨ ((p2 ∨ (p3 ∨ p4)) ∨ p4)) ∧ p5)) → (p3 → ((False ∧ ((False → True) ∧ p4)) ∧ p4))) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185091479925966169237634497118 : (((p4 ∨ p2) ∨ ((True ∨ (((p3 ∨ p3) ∨ p1) ∨ True)) ∧ p5)) ∨ ((p2 ∧ ((((p5 → (False ∨ p5)) ∨ True) → True) → (True → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129199881905222103809928776809 : (((((((p5 → p4) ∨ p4) → p2) → (((((True → True) ∧ True) ∨ True) → p1) ∨ p3)) → (p5 ∨ (p4 ∨ True))) ∨ p1) ∧ (False → (True → False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118792260534502856779292780756 : ((p5 ∨ (p3 → (((p3 ∨ True) ∧ ((False ∧ False) ∧ ((p5 ∧ (p3 → False)) ∧ (((p1 → p4) ∨ p1) ∨ False)))) ∧ (p1 ∧ p3)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244252637903088524623482553964 : ((False ∧ True) ∨ ((p2 ∨ ((((((((p5 ∧ p2) ∧ ((p4 ∧ p4) ∧ ((p4 ∧ p2) ∨ p4))) ∨ False) → p5) → p5) ∨ False) ∧ True) ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56158517129681044820202094953 : (((True ∧ (p3 ∨ (p2 → p5))) ∨ (((True → (p1 ∨ p2)) ∧ p4) → ((((p2 ∨ ((p1 ∨ p1) ∧ p3)) ∧ (p2 → p4)) → p3) ∨ p4))) ∨ p3) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328428595884005034224782656233 : (True → ((p3 ∧ ((((p5 ∧ (((p4 → p4) ∨ True) ∧ (p4 → p3))) → p4) → p3) → (True ∧ p4))) ∨ (((p5 → (p4 ∧ p1)) ∧ True) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157690844366617749276106386602 : (((p3 → ((p2 → (False ∨ ((p4 ∨ False) ∧ ((p2 ∧ True) → False)))) ∧ p2)) ∨ (p2 → (p2 ∧ False))) ∨ ((p1 ∨ (p2 → (p5 → p5))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218793006373369016552303049711 : ((p1 ∧ (p2 ∧ (True ∨ p4))) → (((p4 ∨ p3) → ((((p4 ∨ True) → False) ∨ p4) ∨ True)) ∨ ((True ∨ (((p5 ∧ True) ∧ False) ∧ p2)) → False))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
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
theorem thm_5_vars_48008213419373191358353649915 : ((((p3 ∧ (p1 ∧ (((p5 ∧ ((p2 ∧ p1) ∧ p5)) ∨ (p2 → True)) ∧ p3))) → (p5 ∧ (False ∨ ((p4 ∨ p2) → p1)))) → (p2 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_451477391332282387216876380978 : (((((((False ∧ True) ∧ (p3 ∨ True)) ∧ (((p1 → (p5 ∨ p3)) ∧ p2) ∧ p1)) ∧ ((False → False) ∨ True)) ∨ (p5 → (p5 → (p5 → True)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157788912640897849570322708107 : ((((p4 ∨ (p5 ∧ p1)) ∧ ((p1 → p3) ∧ ((True ∧ False) ∨ p4))) ∨ ((False ∨ p3) ∧ (False ∧ False))) ∨ (p2 ∨ (((False ∨ p5) ∨ True) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723673448753242360802689464757 : (((((p5 ∨ p3) → True) ∧ (((p4 → True) → p4) ∧ ((((p3 ∧ p1) ∨ ((p4 ∨ (True ∨ p2)) ∧ (p1 ∧ True))) ∧ p4) → (p2 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340817940281056708200617866531 : (p2 → (((((p4 → ((((((True ∨ True) → ((p3 ∨ p2) → False)) → (p3 ∧ True)) ∧ False) ∧ p2) ∧ True)) → p1) ∧ p3) ∨ (p2 ∧ p2)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748529655601348399425233888623 : ((((p3 → True) → (False ∨ (((p3 ∨ p4) ∧ p5) ∧ (p3 ∧ (p2 ∨ ((p4 → (((False → (False → p5)) ∧ (p2 ∨ p5)) ∨ p2)) ∧ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614088980267104247098297411678 : (((((p2 ∨ ((True ∨ p1) ∧ (((p2 ∧ (p2 → p5)) ∧ (True ∧ ((p3 → True) ∧ (p5 ∧ p5)))) → p1))) ∨ ((p2 ∨ False) ∧ False)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149465867485113728651235934603 : ((False ∧ ((p4 ∧ (p5 ∧ False)) ∧ ((False ∨ (p2 ∨ ((p2 → p1) ∨ (p3 ∨ (p1 ∧ p3))))) ∧ (p3 ∨ True)))) ∨ (p1 ∨ (p3 → (True ∨ p4)))) := by
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
theorem thm_5_vars_964075725804782663587743917885 : ((((p5 → False) ∧ (p5 ∧ ((((((p3 → p2) ∨ p5) ∧ ((p4 ∨ (p3 ∧ True)) ∧ p1)) ∨ ((True ∧ p4) ∨ p2)) → (p1 ∧ p2)) ∨ False))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37293105540765078519035253726 : ((((p5 ∨ (((((((p2 ∧ (True → (p3 ∧ p2))) → False) ∨ True) ∧ (p1 ∨ p2)) ∧ (True ∧ p4)) ∧ p1) ∧ (False ∧ p4))) ∧ False) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265539144670493028142115667309 : (True ∧ (False ∨ ((p2 ∨ (p3 ∧ (p5 ∧ (p2 → p5)))) ∨ (False → ((((p2 ∨ (p5 ∨ (True ∨ (p4 ∨ (False ∨ p1))))) ∧ p1) ∨ p1) → p5))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h1
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h1
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- False on the left can always be used.
          apply False.elim h1
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- False on the left can always be used.
            apply False.elim h1
          case inr h13 =>
            -- Disjunctions on the left can always be decomposed.
            cases h13
            case inl h14 =>
              -- False on the left can always be used.
              apply False.elim h14
            case inr h15 =>
              -- False on the left can always be used.
              apply False.elim h1
  case inr h16 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625269169714407535837155532484 : ((((True → (True → ((p2 ∨ True) → ((((p1 ∧ p2) ∨ p1) ∧ (p4 ∨ p5)) → ((p5 ∧ (False → (p2 ∨ p5))) ∧ (p2 ∨ p1)))))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_46992650998985352638470987447 : (((((p5 → ((True ∧ (p3 → (p1 ∨ False))) → (True ∧ False))) → (((p1 ∧ False) ∧ ((p3 ∨ p2) → p3)) → True)) → False) ∨ (False → p3)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185315602623898012278194576369 : ((p3 ∧ ((((p5 → p5) ∨ p4) → (p2 ∧ p3)) ∧ (p4 ∨ p2))) ∨ (p2 → (((False ∨ (((p2 ∧ (p2 ∨ p5)) → False) → p3)) ∨ False) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p2 ∧ (p2 ∨ p5)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57727854958544665842081529815 : ((((p1 ∨ p5) → True) → (((p4 ∨ p2) ∧ p5) ∨ ((((p5 ∧ (p2 ∨ p4)) ∧ p3) ∧ (p2 ∨ p2)) ∧ (((p5 → p3) ∧ p1) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57735281336936926909598915349 : ((((p3 ∨ p5) → False) → ((p2 → True) ∧ ((p5 ∨ (p5 ∧ (False ∨ p1))) ∨ (False ∨ ((p2 ∧ (p2 ∧ (p1 ∧ (p3 ∧ p2)))) → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41246354661427114666001197928 : ((((((((p1 ∧ p3) ∧ p3) → p4) → (p1 ∧ ((((True ∨ True) ∧ p4) ∧ True) → p4))) ∨ False) ∨ (p5 ∨ (True ∨ (p3 ∨ False)))) ∨ p3) ∨ p5) := by
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
theorem thm_5_vars_67948407081939344335619559191 : ((p2 → ((False → ((p5 → p2) ∨ (False ∧ p3))) → (((((p2 ∨ p2) ∧ True) → True) → False) → (p3 ∧ (p3 ∨ (p5 ∨ (False → p1))))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p2 ∨ p2) ∧ True) → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173220612439932073452051892829 : ((p5 ∨ (p3 ∨ (p3 ∨ ((p4 ∨ (p1 ∧ (p1 → ((False → p3) ∧ p3)))) ∨ p1)))) ∨ (((True ∨ (True → True)) → ((p4 ∨ p5) ∨ False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118238533288702072149823515512 : ((p1 ∨ ((p1 → (p2 ∨ (((p4 → ((p3 ∨ (p5 ∨ (False ∧ p2))) → (p5 ∨ (p1 → p4)))) ∨ (False ∧ p4)) → False))) → p1)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257204402123987755933905055892 : ((p2 ∨ p2) → ((((p5 ∨ p4) → (True → (p3 ∧ (((p5 ∧ False) ∨ (p1 → False)) ∧ p1)))) ∨ p5) ∨ ((True ∧ (p1 ∨ (p2 ∧ p3))) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57353577492696987554780791446 : (((p3 ∧ (p5 ∧ p5)) ∨ (((p2 → (True ∨ p5)) → p3) ∨ (((((p3 ∨ p4) → False) ∧ (p5 ∨ p4)) ∨ (False → (p1 → p3))) ∨ False))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257647351700780474329770671826 : ((p3 ∨ p2) → (True ∧ (p1 → ((p2 ∧ (((((p4 ∧ (p2 → p2)) → ((False ∨ p1) ∨ p4)) ∨ (p4 → (p4 ∧ p3))) ∧ p5) ∧ p1)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_356629003533262640488142151239 : (p5 → (((p4 ∨ p4) ∧ ((p1 → (p5 ∨ True)) ∧ p4)) ∨ (True ∧ ((p2 ∧ p3) → (False ∨ (((p3 ∨ ((p3 → False) ∨ p3)) → p1) ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249038365568157690801025203361 : ((p4 ∨ False) ∨ (p4 → ((((p5 ∧ False) ∧ (p5 ∨ False)) ∨ ((True ∨ ((p4 ∨ ((True ∨ p3) ∧ p5)) ∧ (False ∧ (False ∨ p1)))) → p2)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117734265036546885715599156006 : ((p4 ∧ ((((p2 ∨ (p4 → (((p1 ∧ p4) ∧ p5) → p3))) ∨ (p5 ∨ (p2 → (p4 → ((p3 ∨ p1) → False))))) ∧ p4) ∧ False)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350148060960758821387682211345 : (p4 → ((((p3 ∧ (p3 ∨ ((False → p4) ∨ (p5 ∧ p5)))) → False) ∧ (p3 ∨ (((((p1 ∧ p5) ∨ p1) ∨ p5) → p5) → (p3 ∨ p2)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327223758448952213184980759838 : (True → ((p2 → (((((p1 ∨ p5) ∧ True) ∨ (((p5 ∧ True) ∨ (((p5 ∧ False) ∨ False) ∨ p3)) ∨ (p5 ∧ p5))) ∨ True) ∨ (p1 ∧ p3))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259212763160617396175005530295 : ((False → False) → (((False → p3) ∧ ((p1 ∧ (p2 ∨ (p2 ∨ p1))) ∨ p4)) ∨ ((p5 → (p3 → ((p5 ∨ ((p2 ∨ False) → p3)) → p3))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208022446771369719927549252056 : ((((p2 → p2) → p1) ∨ (p5 ∧ p2)) → ((((p2 ∨ ((p3 ∧ p2) ∧ ((p5 ∨ False) ∧ False))) ∨ (p1 ∧ (p1 ∧ p2))) ∨ p1) ∨ (p4 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (p2 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646325503729402758543510240670 : ((((False → (False ∧ (((p2 ∧ ((((p2 → p3) ∧ False) → p5) → p2)) ∧ ((p4 ∧ True) ∧ (p3 ∧ (p5 → (True → p1))))) → True))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150339437586431847098262680684 : ((p5 → (((p3 ∨ ((False ∨ True) ∧ (((((p5 ∧ False) ∧ p5) ∨ False) → True) → p2))) ∨ p2) ∧ (p3 ∨ p3))) ∨ (p4 → ((p3 ∨ p2) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703396105568773027657766202746 : ((((p2 ∨ ((((p2 ∧ p5) ∨ p3) ∨ (False → p2)) ∧ False)) ∨ ((p5 → (False → ((p2 → p5) ∨ (p5 ∨ (p4 ∧ (p5 ∧ p4)))))) ∨ p5)) ∨ p1) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586918735490991238973449535906 : (((((p1 ∨ (((p5 → (False ∧ False)) → (p5 ∧ True)) ∧ ((((True ∧ (p3 ∧ p3)) ∨ (p3 ∧ p3)) → False) ∧ (p1 ∨ p4)))) ∧ p3) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50494225708448732784339657892 : (((p5 → ((False ∧ p2) ∨ ((True → (p1 ∨ (p3 ∧ True))) ∨ ((True ∨ True) → ((p4 ∧ p1) → p2))))) ∨ ((p5 → (False ∨ False)) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215796490930484384495825617625 : ((p1 ∨ (p3 ∨ (p2 ∧ p5))) ∨ (((p4 → True) ∧ (p1 ∨ (p3 ∨ ((p4 ∨ ((True ∨ p4) ∧ True)) ∨ ((False ∧ False) ∨ (p3 ∨ p4)))))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730673047947715957639532594106 : ((((p3 ∧ (p4 ∧ p1)) → (((p1 ∨ False) → False) → ((p4 ∧ ((p2 ∨ (((p5 ∧ True) ∧ False) ∧ (p5 ∧ True))) ∨ (p1 ∧ p5))) ∨ p3))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181543524500916168462350917907 : ((True → (p3 → (((p2 → p5) ∧ False) ∨ (True → ((p5 → False) → p5))))) → ((p1 → ((((True ∧ False) ∧ False) ∧ p5) ∧ (False → p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40510934768802789507647866204 : ((((p3 ∧ ((p3 ∨ ((((p3 ∨ (p2 ∨ ((p2 ∨ p5) ∧ (p3 ∧ False)))) → p2) ∨ False) ∨ ((True → p2) → False))) ∨ True)) ∨ p2) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351912637686401763044226459894 : (p4 → (((False ∨ p2) ∧ ((p2 ∨ (False ∨ p5)) ∧ (p5 ∨ p3))) ∨ ((p3 ∨ (((True ∧ (p5 ∧ p4)) → (p5 ∧ p3)) → (p5 ∨ False))) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357454045490305130602131190533 : (p5 → ((p1 → p1) → ((((True ∨ p1) ∧ ((p2 ∨ p5) ∧ False)) ∧ ((p2 → p3) ∨ ((p3 ∨ (False ∧ False)) → (p2 ∨ p1)))) ∨ (True ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158567228768657295375084027942 : ((True ∧ (((p5 ∨ ((p2 ∨ p3) ∨ p3)) ∧ ((((p1 ∧ p2) ∧ p2) ∧ p5) → p5)) → (False ∧ True))) ∨ (((p3 ∨ p3) → (p2 → True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208168692722642956137879112641 : (((p2 ∧ (p1 → p1)) → (False ∨ p5)) → ((p2 ∨ (p4 → ((p2 ∨ False) → p3))) ∨ ((((p3 → p1) ∨ (True ∨ p5)) ∨ p2) ∨ (p1 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713714954024834298343765607523 : (((((p1 ∨ (True ∧ (p3 ∨ p2))) ∧ p5) → ((False ∨ (((((p1 → (p3 ∨ True)) ∧ p2) → p1) ∨ p3) ∨ True)) ∨ ((False → p5) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158377282049562265228196771439 : (((True → True) ∧ ((False ∧ (((p5 ∨ p3) ∨ True) → False)) ∨ (p1 → ((p2 ∨ (p3 → p3)) ∨ p2)))) ∨ ((p4 ∧ ((False ∧ p5) ∧ p2)) → p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85942980881796964462473704868 : ((((((p4 → ((p1 ∨ p2) ∧ False)) → p2) ∨ False) → p1) ∧ (((((False ∨ False) → (p4 → ((True → p4) ∨ True))) ∧ p2) ∨ p1) ∨ p2)) → p1) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : (((p4 → ((p1 ∨ p2) ∧ False)) → p2) ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h8
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : (((p4 → ((p1 ∨ p2) ∧ False)) → p2) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h13
    -- One of the premise coincides with the conclusion.
    exact h15



