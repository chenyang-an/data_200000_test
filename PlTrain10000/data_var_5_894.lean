variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186500299121642370099838439590 : (((p1 ∨ (((p2 ∧ True) → p1) → (p1 ∨ p5))) ∧ (True ∨ p5)) → ((p2 ∨ ((p3 ∨ p1) ∨ ((True ∧ p1) → (p2 → p4)))) ∨ (p4 → p4))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190977135910913409383420303398 : (((((p1 ∧ False) ∨ p2) ∨ p4) ∨ (p5 ∨ (p2 → p1))) ∨ ((((p4 ∧ (p3 → ((p4 ∧ False) ∨ (True ∨ p2)))) ∧ p2) ∧ (p5 ∧ p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248651414467012599956795440093 : ((p3 ∨ p1) ∨ (((True ∨ p1) ∨ p5) ∧ (p3 → (((p5 ∨ (p5 → p1)) → (p2 ∨ (p4 ∨ (p2 ∨ (p3 ∧ True))))) ∧ ((p2 → p3) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327863672536095773636799986452 : (True → (((False ∧ p5) ∧ (p4 → ((p4 → ((p2 → False) ∨ (p1 ∨ p4))) ∧ ((p1 ∨ (p1 ∧ p5)) → (p5 ∨ (True → p3)))))) ∨ (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199076436885213701384334076581 : (((((p5 → p2) ∧ (p4 → p3)) → p4) ∧ p4) → (((p4 → False) ∨ ((p5 ∧ (True ∧ True)) ∨ ((((False → True) → p2) → p3) ∨ p4))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66163497001568051466852759820 : ((p5 ∨ ((p2 → (p4 ∧ (p3 ∨ ((((p5 → ((p4 ∧ False) ∧ p3)) → ((True → p5) ∧ p1)) → True) ∧ p3)))) ∧ ((False ∧ p2) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56718184686652358221296160385 : ((((False ∨ True) ∨ False) ∧ (False ∨ ((p2 → (p5 ∧ False)) ∨ ((True → ((p1 ∧ False) ∧ False)) → (((p5 → False) ∧ (p1 ∨ p2)) → p2))))) ∨ False) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183985708195753866188444662643 : ((((((p5 ∨ p2) ∧ (p3 → p2)) ∧ (p3 → p5)) ∧ p3) ∨ p5) ∨ ((True ∧ p4) ∨ ((False → False) ∨ ((p3 → (p3 → (p1 ∧ True))) ∧ p1)))) := by
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
theorem thm_5_vars_691862110917004705177313992444 : ((((False → ((((p2 → p5) → ((True ∧ (p2 → p3)) ∧ p4)) → p5) ∧ (p4 ∨ p1))) → ((p4 → (p5 ∧ p3)) → (p1 ∨ (p4 ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148779229165089747363009456861 : ((((p2 → (True ∨ p5)) → (p3 → False)) ∨ (((p1 ∨ ((p1 ∨ p5) ∨ p3)) ∧ ((p4 ∨ True) ∨ p4)) ∨ False)) ∨ ((p1 ∨ False) → (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174540495686476849689264072668 : (((p2 ∧ (False → ((p5 ∧ True) ∧ p3))) → (((p1 ∧ p2) ∨ p1) → (p2 ∧ p2))) → ((((((p5 ∧ p4) ∧ p4) ∨ p4) ∧ p4) ∨ True) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192765516625849934628883010936 : (((p2 ∧ ((((p5 → p5) ∨ p5) ∧ p5) → p3)) → p3) → (((p2 ∨ (((p2 ∧ p4) ∨ (p4 ∧ True)) ∨ (p1 ∧ True))) ∨ True) ∨ (False ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164518404477028026618851871433 : (((((p5 ∨ p4) ∨ (p2 ∧ (p3 ∨ (p4 → ((False ∧ p2) ∧ p4))))) ∨ (False ∧ p3)) ∧ p1) ∨ ((p5 → p3) → (p3 ∨ (False ∨ (False → p2))))) := by
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
theorem thm_5_vars_136220346703986831723484455256 : (((((p1 ∨ p2) ∧ (p4 → p1)) ∨ False) ∨ ((False ∧ ((p5 → p1) ∧ ((p2 ∨ p1) → p2))) ∨ ((True → False) ∧ p3))) ∨ ((False ∨ p1) → p1)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103119837877640689648771361905 : ((((p2 ∧ (p2 → p5)) → (p4 ∨ (((((p4 ∧ True) ∨ p3) → (p4 ∧ p1)) ∨ ((True ∨ p5) ∧ p1)) ∨ (False ∧ p2)))) ∨ True) ∧ (True ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198593863732782962758892867953 : ((p2 ∨ (((False ∧ (p2 ∧ p4)) ∨ p4) ∨ p3)) ∨ ((p1 ∨ p1) → (p1 ∨ ((p4 ∧ ((p5 ∨ True) → (((p5 ∧ p1) ∧ p1) ∧ p4))) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174137722714164793653862104032 : ((((((False ∧ p5) → p5) → ((p4 → (p2 ∨ p2)) → p1)) ∨ p2) ∨ (p2 → False)) → ((p2 ∧ (True → (False ∧ (True → (p2 → p1))))) ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149625226349065116504273097727 : ((p4 ∧ (((((False → p1) → ((p4 ∨ True) ∧ (False ∧ (True → p1)))) → ((True → p5) → False)) ∧ True) ∧ p1)) ∨ (((p2 ∧ p5) ∧ p3) → p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212952460224229544025007462635 : ((p4 → ((p3 ∨ p2) ∨ p4)) ∧ ((((False ∨ p4) → ((False → True) → (p1 ∨ True))) → False) → ((p2 → p2) ∧ (False ∨ (p5 → (p4 → False)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∨ p4) → ((False → True) → (p1 ∨ True))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h4
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148025719006821521805900200670 : (((((p3 ∨ (p4 ∧ p5)) ∨ p4) ∧ ((p2 → (p3 ∧ p3)) ∨ ((p2 ∨ (False ∧ p1)) → p3))) ∨ (p2 → p1)) ∨ ((p1 ∨ True) ∨ (p1 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201241531771272141251515417966 : ((p2 → (p4 → (True → ((False ∧ True) → p5)))) → ((p2 → (((p3 ∨ p4) ∧ (p5 ∨ (((False ∨ p3) ∨ (p5 ∧ p3)) → p1))) ∨ True)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157629101793441809827320127397 : (((((p4 ∧ p2) ∨ p4) ∨ ((False ∧ (False ∧ (False → (p1 → p4)))) ∧ p2)) ∧ ((True ∧ False) ∨ p2)) ∨ (True ∨ (((p5 → True) ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134936980737879835061583952897 : ((((((p4 → False) → (p4 → ((p2 → p1) → (p2 → (p1 ∨ (p4 ∨ False)))))) → p2) ∧ (p1 ∨ p5)) ∧ (True ∨ p4)) ∨ (p1 → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613017092930079227281763757851 : (((((((p1 ∨ p5) → (((p2 ∨ (((p3 → p5) ∨ p3) ∧ p1)) ∧ (True → (p3 ∧ p2))) → (False ∨ p1))) ∧ p2) → (p3 ∨ p3)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_227510294923806469798871854518 : ((True ∧ (p2 ∨ p3)) ∨ (((p1 ∨ (True → ((p5 ∨ (True ∨ p5)) ∨ True))) ∧ p2) ∨ (p5 → ((((p5 → True) ∨ (p5 → p5)) ∨ p1) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183951377600972555123828664825 : (((p4 ∨ (True ∧ ((p1 ∨ (p3 ∧ (True → True))) ∧ p4))) ∧ True) ∨ (p5 → ((((p2 ∧ ((p2 → p5) ∧ False)) ∧ p3) ∨ (p4 ∨ True)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_114869567918845760474986068912 : ((((((p4 ∧ p3) ∧ True) ∨ (p2 ∧ p3)) → ((p1 → p5) → (p1 ∧ p3))) ∨ (False → (((p2 ∧ p4) ∧ (True ∨ p4)) ∧ p1))) ∨ (p1 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257574495239538165156496162136 : ((p3 ∨ p1) → ((p2 ∨ ((p5 ∨ p4) → (False ∨ (p1 → True)))) ∨ (p5 → (((True ∧ (p4 → ((p3 ∧ p4) → (p3 ∧ False)))) → p2) ∧ p1)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
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
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136267099258982855560374206370 : ((((p4 ∨ (p1 → (p2 ∧ p3))) ∨ p3) → ((((p2 → ((p1 → ((True ∨ p3) ∧ False)) → False)) ∨ p4) ∧ p2) ∧ p4)) ∨ (True ∨ (p4 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52616743631333646067813506605 : ((((True ∧ (p3 ∧ p5)) ∧ ((True ∨ (False ∨ p4)) → (p2 ∧ (p2 → p3)))) ∨ ((p3 ∧ ((p2 ∧ (True ∨ p5)) ∧ p5)) ∨ (False ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113582827212184515678706281284 : (((p2 ∧ (((((((p4 ∧ p5) ∨ (False → (p4 → (True → p2)))) → p5) ∨ (p2 ∧ True)) ∧ True) → p2) ∨ p5)) ∨ (False → p5)) ∨ (p5 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50261402049215470576280876552 : ((((p4 → ((((p1 → p4) ∧ False) ∧ (((p5 → False) → (False ∨ (p3 ∨ p5))) ∧ True)) → True)) → p4) ∨ (True → (p2 → (p1 ∨ p2)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184740600877799924284059321801 : ((((p3 ∧ (p2 ∨ p1)) ∨ p4) ∧ (True ∧ ((p1 → False) ∨ p1))) ∨ (True ∨ ((((False → ((p3 ∧ p4) ∨ True)) ∨ (p5 ∨ p5)) ∧ p1) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768488835928517267090394758611 : (((p5 ∧ ((((p5 ∧ (((((True ∧ p1) → True) → p5) → True) ∧ p3)) ∨ (p1 ∧ p5)) ∨ False) ∨ ((p1 → (True ∧ (False ∨ p3))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_435505832744533325142091328248 : ((((((((p5 → (False → False)) → False) ∧ ((p1 → p2) ∨ False)) ∧ True) ∧ ((p5 → (p4 → (p1 ∧ True))) → (p5 → p2))) → (p5 ∧ p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : (p5 → (False → False)) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h12 := h6 h9
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h20 =>
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h21 : (p5 → (False → False)) := by
      -- Implications on the right can always be decomposed.
      intro h22
      -- Implications on the right can always be decomposed.
      intro h23
      -- False on the left can always be used.
      apply False.elim h23
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h24 := h18 h21
    -- False on the left can always be used.
    apply False.elim h24
  case inr h25 =>
    -- False on the left can always be used.
    apply False.elim h25
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678834518803377964030058380997 : ((((False ∧ (p2 ∧ (((False → p4) ∨ p1) → ((((p4 ∧ p1) ∨ (p2 ∧ (p5 → p3))) ∨ p3) ∧ False)))) ∨ ((True ∧ (p4 ∨ True)) ∨ False)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47273491627090515111149144887 : ((((p2 → ((p2 ∧ p3) → True)) ∧ (((((False ∨ p2) ∧ (p3 → True)) ∧ (p4 → False)) ∧ (p3 ∧ (False ∨ p5))) ∨ False)) ∨ (True → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232209115441327239856434986558 : (((False → p5) → False) → (p3 ∨ (((True ∧ (True ∨ (p2 → False))) ∧ p5) → (((True → p3) ∨ (False ∨ p2)) → (p4 → (p3 ∨ (p1 ∧ p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p5) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134687158233631109800811981803 : ((((p2 ∧ (p3 → ((True → p1) ∨ True))) ∨ (((False ∨ p2) → False) ∨ ((((p2 ∧ p3) ∨ p4) → True) → p3))) → False) ∨ (True ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193581078358311706354363868787 : (((p5 ∨ p1) → (True ∧ ((False → p1) → (True → p3)))) → ((True ∧ (p3 ∨ (((p5 → (False ∧ (p1 ∧ p4))) ∨ p5) → p4))) ∨ (True ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40526822224409041434047103431 : ((((False ∨ (((False ∧ ((p5 ∧ (p5 ∧ False)) → False)) ∧ p3) ∧ (((False ∧ p1) ∧ ((p1 → p4) → True)) ∨ (p4 → p5)))) ∨ False) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809959029569280290586238125361 : (((p5 → (((((False ∨ (p1 ∨ ((p1 → p1) ∨ p1))) ∧ p1) ∧ (False ∨ p5)) ∨ ((p2 ∧ p5) ∨ (False → p4))) ∨ ((p2 → True) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115332617652385506155173775120 : (((p3 ∧ ((p3 ∧ (p5 → (True ∨ p2))) ∧ (p1 ∨ p5))) → (((False ∨ (p3 ∧ (False ∧ (p3 ∧ p4)))) ∧ (p5 ∨ False)) ∨ True)) ∨ (p5 → p1)) := by
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
  cases h5
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46236273708974010022580537031 : (((((True ∨ (False ∨ ((((p5 ∧ (p4 ∧ p3)) → False) ∧ p3) ∨ p2))) → (True ∧ (False ∧ (True → True)))) ∨ (p2 → p5)) ∧ (p1 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190931958470654386405974314540 : (((((p3 ∨ True) → p1) → False) ∧ ((False ∨ p5) ∨ p2)) ∨ (True ∨ (((((p2 → p3) ∨ False) → p3) ∨ p4) ∨ ((p1 ∧ p5) ∧ (False ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53293455476826358640733111263 : (((p1 ∨ ((((p3 ∨ p3) ∨ p3) → ((p1 → p1) ∧ p2)) ∨ p1)) ∨ (p5 → ((False ∨ p3) ∨ (p1 ∨ ((p1 ∨ p5) ∨ (False ∧ p5)))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714572056679382157316888596174 : (((((p4 ∧ p5) ∨ ((p5 ∨ p5) ∨ p2)) → ((((p5 → (((True → p3) ∧ (p2 ∨ (True ∨ (True ∧ True)))) ∧ p2)) ∨ p2) → p1) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50111625077248915726339168830 : (((False ∨ ((p3 ∧ (((p1 → p1) → (p4 → (False ∨ ((p5 → p4) ∧ (False → p4))))) → False)) ∨ p5)) ∧ (p2 → ((p2 ∨ p5) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251319212394963275763389840091 : ((p2 → p3) ∨ (((p5 ∧ p1) ∧ ((p1 ∧ p1) → (False ∧ False))) ∨ (p3 → (((p4 → (p2 ∨ p4)) ∧ (False ∧ (p5 → (p3 ∨ True)))) ∨ True)))) := by
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
theorem thm_5_vars_909223402690520187312290365502 : ((((((p1 → p4) ∨ ((True ∨ p1) ∧ True)) → (((p5 ∧ p1) ∧ (p1 ∧ (p2 ∧ p3))) ∧ p3)) ∧ ((((p3 ∨ p1) → p1) ∨ p4) ∧ p2)) → p1) ∧ True) := by
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
  cases h4
  case inl h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : ((p1 → p4) ∨ ((True ∨ p1) ∧ True)) := by
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
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : ((p1 → p4) ∨ ((True ∨ p1) ∧ True)) := by
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
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h13
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- One of the premise coincides with the conclusion.
    exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_860211427463555686106388335591 : (((((p2 ∧ (((p1 ∨ p5) ∨ ((p2 ∨ (p5 ∨ ((((p1 ∧ p3) → p5) ∨ True) ∨ False))) ∧ (p3 ∧ p5))) ∨ p2)) ∨ (True ∧ True)) → p4) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∧ (((p1 ∨ p5) ∨ ((p2 ∨ (p5 ∨ ((((p1 ∧ p3) → p5) ∨ True) ∨ False))) ∧ (p3 ∧ p5))) ∨ p2)) ∨ (True ∧ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165649967779328769377543634022 : (((((p4 → (p2 ∨ p4)) → False) ∨ p5) ∨ ((p5 ∧ ((p2 → p1) ∧ p2)) ∧ (p1 ∨ p3))) ∨ ((True ∨ True) ∨ (((p5 ∧ p1) ∧ p2) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184538847519699474295889304945 : ((((p4 → (True ∧ (p1 ∧ (p4 ∨ p2)))) ∧ p3) → (p1 ∧ p4)) ∨ ((p5 → (((p5 ∧ (p5 ∧ (p5 ∧ False))) ∧ (p5 ∧ p4)) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50148721017558850036587224911 : (((p1 → (((p4 ∨ p5) → (p3 → (True ∨ p1))) ∧ ((((p4 ∨ (p5 ∨ p1)) ∨ False) → p5) ∧ p4))) ∧ (((p2 ∨ p1) ∧ p1) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658041857172980428506775652823 : ((((p3 ∧ ((True ∧ ((((p1 ∨ p1) ∨ (p4 ∨ p5)) ∧ ((p2 ∨ p3) → True)) ∧ ((p3 → (p3 ∧ p1)) → p4))) ∧ p4)) ∨ (p5 ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_113263320997438731039286066190 : ((((p5 → ((((p2 → p4) → p5) ∨ p1) ∧ ((False → p3) ∧ ((p5 ∧ p4) ∨ False)))) ∧ (False ∨ (p2 ∧ p4))) ∧ (p5 ∧ p4)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54007870894549148689390184740 : ((((((p1 ∨ (p5 → p4)) → p4) → (p1 ∧ True)) → p3) → ((p4 ∧ p2) → ((p2 ∧ ((p2 → p1) ∨ ((p5 ∨ False) → p5))) ∧ True))) ∨ False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747528882825171554362911626166 : ((((True → p2) → ((((p1 → ((True → p1) ∨ p3)) ∧ p1) ∧ ((True → False) → (True → (p5 ∨ p4)))) ∧ (False ∧ (p2 ∧ (True ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55120267575341325005393752031 : (((((True ∨ False) ∧ (p4 ∧ p3)) ∧ p1) ∨ ((True → (p1 ∨ (True ∧ ((p2 → p3) ∨ p3)))) → (p4 ∨ (False ∨ (p5 → (p2 ∨ p5)))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654088561607876051515254259983 : (((((p4 → ((((True ∧ (p3 ∨ p3)) ∨ p4) → ((((p5 ∨ (p2 ∨ False)) ∧ (p1 → p3)) → False) ∨ p2)) ∨ False)) ∧ p1) ∨ (p5 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261218771810234786448482660594 : ((p4 → p5) → ((p1 → (((True ∧ True) ∨ (p1 → p3)) → True)) → (p3 ∨ (True ∨ (((p2 ∧ p5) ∨ p2) ∧ (p3 ∨ (p4 ∨ (p2 → p4)))))))) := by
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
theorem thm_5_vars_231778609427270067638181369849 : (((p3 ∧ p5) → p3) → (p2 → ((p1 ∨ ((p2 → (p4 ∧ p1)) → p5)) ∨ ((p4 ∨ (((p4 → p2) → (True ∧ False)) → p5)) ∧ (False ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p4 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171553079019760450250077649157 : ((((((p4 ∨ p1) ∧ (p5 ∧ (p5 → p2))) ∧ ((p4 → p4) → p3)) → False) ∨ True) ∨ (p4 ∨ (p1 ∨ (p4 ∨ (False → (p5 ∨ (p5 ∧ p4))))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_222305393815567352316434420593 : (((p1 → p1) → True) ∧ (((((((True ∨ ((True ∧ p4) ∨ (p5 ∨ True))) → ((p5 ∨ True) ∨ True)) ∧ False) ∨ p3) ∧ False) ∧ (p3 → p2)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113501334231835817138265944573 : ((((True ∨ ((p4 ∨ True) → ((((p3 ∨ ((True ∧ p1) ∧ p2)) ∨ p2) ∧ False) ∧ p2))) → ((False ∨ True) ∧ False)) ∨ (False → p4)) ∨ (True → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187762598236525878213263925085 : ((p2 → ((p2 → p4) ∨ ((((p5 → p4) ∨ p2) → p3) ∧ p2))) → (((p1 ∨ p5) ∨ True) ∧ ((p5 → ((p1 ∨ p3) ∨ (p1 ∨ p5))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258658463066290413477170848946 : ((p5 ∨ p5) → ((p1 → (((p4 → (p2 → False)) ∧ p4) ∧ ((((p5 ∨ p3) ∨ p3) ∨ True) ∨ (True → (False → False))))) ∨ ((p4 ∨ True) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49129155248705155583289707259 : (((((p5 → False) → (p5 ∧ (((False ∨ True) ∨ p1) ∧ (False ∧ p1)))) ∨ (p4 ∧ (p3 → ((p3 ∨ p3) ∧ p4)))) ∨ (p2 ∨ (True ∨ p5))) ∨ False) := by
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
theorem thm_5_vars_147328975705816333200163988557 : ((((p2 ∨ (((p2 ∨ (p1 ∨ (p2 → ((p2 → p3) ∧ (p4 ∨ False))))) ∧ p2) ∧ p2)) ∧ (p5 → p5)) ∨ p5) ∨ (True ∨ (p2 ∨ (p4 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33274476050783904598353723976 : ((p4 ∨ (((False ∧ ((p4 → ((p1 ∧ p2) → (p3 → ((True → False) ∧ False)))) → ((p2 ∧ p5) ∧ p5))) ∨ (p2 → (p2 ∨ True))) ∨ p1)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63887660267093243435329401598 : ((False ∨ (((p2 ∨ ((((p5 ∧ p4) ∧ (True ∨ (((((p4 ∨ p1) ∧ (p3 ∧ p3)) ∨ p3) ∨ p2) ∧ p1))) ∨ p3) ∨ True)) ∨ False) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137849100789485720431498522905 : ((p3 ∨ ((p2 ∨ (p5 → p3)) ∨ ((((((p4 → ((False ∨ False) ∨ (p3 ∨ p5))) ∧ True) ∨ p3) → p2) ∨ p2) ∨ p3))) ∨ (p5 → (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143314650398097516307534215147 : ((p4 → ((p2 ∨ ((((((False → (p5 → p3)) → p3) → (p1 ∨ False)) ∨ p4) → (p3 ∧ (p3 → p1))) ∧ p3)) → False)) → ((p3 ∨ True) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110954274884519847810198763626 : (((((((False ∧ ((p5 ∧ True) ∨ p3)) → (False → p3)) → (p5 → (((p3 → p2) → p3) ∧ False))) → p5) ∨ (p5 ∨ p4)) ∧ True) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172465620486395117031243483061 : (((p1 → ((False → p3) → p2)) ∨ ((p1 → True) ∧ (((p5 ∧ False) ∨ p5) ∧ p1))) ∨ ((((True → p1) ∧ p2) → (p3 ∨ p1)) → (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115524326189934666607845927006 : ((((p1 ∧ False) → (((p5 ∨ p4) ∨ True) ∧ p4)) → ((True → p5) ∧ (p5 ∧ ((((p2 ∧ (p4 ∨ False)) ∧ p3) ∧ p1) ∨ p3)))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197067658039136360649040258806 : ((((p1 ∨ True) → ((p5 ∨ p3) ∨ p1)) ∨ True) ∨ (((((p3 ∨ (p3 ∨ (False ∨ (p1 ∧ p1)))) ∨ p2) ∧ True) → ((False ∧ True) ∨ p4)) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62621856146777501612056680095 : ((p4 ∧ (((p3 → (((((((p4 ∨ True) ∨ True) ∨ p5) ∨ p4) → (p3 ∧ False)) ∧ p4) → True)) ∧ (((p3 ∨ p2) → p5) ∨ p4)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628710528462310891407330114966 : (((((True → ((True → (p4 → p4)) → (p1 ∧ (((((False ∧ (True ∧ False)) ∧ p1) → p4) ∧ (p4 ∨ (p3 → p4))) ∨ p3)))) ∧ p1) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111545556903235307603567358399 : ((((((p2 ∧ p3) ∧ ((((p4 → False) ∨ (p4 ∨ ((False ∨ p4) → (p2 ∧ p5)))) → p5) ∨ p1)) ∧ (p3 ∨ True)) ∧ p2) ∨ True) ∨ (p5 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112500919674294215070122418757 : ((((p3 → ((p4 ∧ p4) ∨ (p3 → ((p4 → False) → (p5 → (((((p5 → p3) ∨ p3) → p1) ∨ p3) → True)))))) ∨ p3) → p3) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158976511621278889331546715911 : ((p3 ∨ ((p3 ∧ (((p1 → ((p5 → False) ∧ ((p3 ∨ p3) ∨ p2))) ∨ p5) → p2)) ∧ (p4 ∧ p1))) ∨ (((p2 ∧ p3) → p4) → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730253452227802965670294407587 : (((((p2 → p2) → False) → (((p4 ∧ (((((p5 ∧ True) ∧ (False ∨ p2)) ∨ p1) ∧ (p4 → p3)) ∧ p1)) ∧ ((p4 → p1) ∧ True)) ∨ p2)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779857528761740131202703756126 : (((p2 ∨ ((True ∨ ((((((p2 ∧ p1) ∨ (p3 → True)) → p3) ∧ (p3 → (False ∧ p5))) → (p2 ∧ p1)) ∨ ((False ∨ True) ∨ p5))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158639791651280551844115722463 : ((p1 ∧ (((True → (((False ∧ p2) ∧ (p5 ∧ p2)) → p1)) → ((p5 ∨ p1) ∧ p4)) ∧ (p4 ∧ False))) ∨ (((p5 → True) ∨ p1) ∧ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156940380847590662088561980099 : ((((((p2 ∨ p4) ∨ p2) ∧ ((((p1 ∨ True) ∨ p1) ∨ p4) → (p3 → p4))) ∨ (True ∧ True)) ∨ p3) ∨ ((p2 → ((p3 ∨ True) ∨ True)) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208239039865514763390923892248 : (((p1 ∧ p3) ∧ (p3 ∨ (p2 ∨ True))) → (((((((p3 ∧ p1) ∧ p3) ∨ p4) → False) ∧ p2) ∧ (((p5 ∨ True) ∧ (p5 → p1)) ∨ p4)) → False)) := by
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
  cases h4
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h1.left
      let h12 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h15 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h16 : (((p3 ∧ p1) ∧ p3) ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h15
          -- One of the premise coincides with the conclusion.
          exact h13
          -- One of the premise coincides with the conclusion.
          exact h15
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h17 := h5 h16
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h20 : (((p3 ∧ p1) ∧ p3) ∨ p4) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- One of the premise coincides with the conclusion.
            exact h14
            -- One of the premise coincides with the conclusion.
            exact h13
            -- One of the premise coincides with the conclusion.
            exact h14
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h21 := h5 h20
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h23 : (((p3 ∧ p1) ∧ p3) ∨ p4) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- One of the premise coincides with the conclusion.
            exact h14
            -- One of the premise coincides with the conclusion.
            exact h13
            -- One of the premise coincides with the conclusion.
            exact h14
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h24 := h5 h23
          -- False on the left can always be used.
          apply False.elim h24
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h1.left
      let h27 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h28 := h26.left
      let h29 := h26.right
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h30 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h31 : (((p3 ∧ p1) ∧ p3) ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h30
          -- One of the premise coincides with the conclusion.
          exact h28
          -- One of the premise coincides with the conclusion.
          exact h30
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h32 := h5 h31
        -- False on the left can always be used.
        apply False.elim h32
      case inr h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h35 : (((p3 ∧ p1) ∧ p3) ∨ p4) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- One of the premise coincides with the conclusion.
            exact h29
            -- One of the premise coincides with the conclusion.
            exact h28
            -- One of the premise coincides with the conclusion.
            exact h29
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h36 := h5 h35
          -- False on the left can always be used.
          apply False.elim h36
        case inr h37 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h38 : (((p3 ∧ p1) ∧ p3) ∨ p4) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- One of the premise coincides with the conclusion.
            exact h29
            -- One of the premise coincides with the conclusion.
            exact h28
            -- One of the premise coincides with the conclusion.
            exact h29
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h39 := h5 h38
          -- False on the left can always be used.
          apply False.elim h39
  case inr h40 =>
    -- Conjunctions on the left can always be decomposed.
    let h41 := h1.left
    let h42 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h43 := h41.left
    let h44 := h41.right
    -- Disjunctions on the left can always be decomposed.
    cases h42
    case inl h45 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h46 : (((p3 ∧ p1) ∧ p3) ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h40
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h47 := h5 h46
      -- False on the left can always be used.
      apply False.elim h47
    case inr h48 =>
      -- Disjunctions on the left can always be decomposed.
      cases h48
      case inl h49 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h50 : (((p3 ∧ p1) ∧ p3) ∨ p4) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h40
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h51 := h5 h50
        -- False on the left can always be used.
        apply False.elim h51
      case inr h52 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h53 : (((p3 ∧ p1) ∧ p3) ∨ p4) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h40
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h54 := h5 h53
        -- False on the left can always be used.
        apply False.elim h54



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614526946484008486451418042406 : ((((((((p4 ∧ (p5 → p1)) ∧ ((p2 ∧ (p1 ∧ p3)) → p2)) ∨ p4) → ((p5 → p4) → p1)) ∧ (((p2 ∧ p2) ∨ p5) ∧ True)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355904251546892838917591695156 : (p5 → ((((False ∨ ((p3 → p2) ∨ p4)) → (p2 ∨ (p1 ∧ (((False ∧ p4) ∧ ((p4 ∧ p2) ∧ p3)) → p1)))) ∨ p3) → ((True → p1) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206414655768296854808792508674 : ((p3 ∨ (p4 ∧ (p1 ∨ (p2 ∧ p4)))) ∨ ((p5 → ((p4 ∧ ((((p5 → p3) ∨ p1) ∧ (p1 ∨ p4)) ∧ p1)) ∧ ((p4 ∨ True) → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47187868047805895430212691875 : (((((p3 ∨ p1) → ((p4 ∧ p4) ∨ ((p1 ∧ (p2 ∨ p2)) ∨ False))) ∧ (((p5 → (p5 → p4)) ∨ (p5 ∨ p1)) ∧ p2)) ∨ (False → p1)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186700196956490758909568287073 : ((((p1 ∨ (True ∨ (True ∧ p1))) ∨ p3) ∨ ((False ∨ p1) → True)) → (p5 ∨ (((True → (True ∨ p5)) → (p5 ∧ p1)) → ((p5 ∧ p3) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h8
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627503603054492511396702241008 : ((((((((((p3 ∨ p3) ∧ p3) → (p1 ∧ p4)) → (((p3 → p1) ∨ (p4 ∨ True)) ∨ p3)) → (p2 ∧ p3)) ∧ (p2 ∧ p5)) ∧ p2) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147701173256122773107816981853 : (((((False → ((p2 ∧ False) ∨ (p5 ∧ p3))) → (False ∧ (True ∨ p5))) → ((p3 ∧ (p4 ∨ p5)) ∨ p3)) → p1) ∨ (((p5 ∨ True) ∨ False) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_336430910773067035576908792259 : (p1 → ((p2 ∨ ((True ∧ (((True → (True ∧ (False ∨ True))) ∨ False) ∧ (((p3 → False) → p2) → (p3 ∧ False)))) ∨ (p1 ∨ (True → p2)))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118458753039991176742208077862 : ((p3 ∨ ((((False ∧ p5) → (p1 ∧ (p3 ∧ (p4 ∧ (p4 → p1))))) → (p3 → (((False ∨ p2) → p3) ∧ (p5 ∧ p4)))) ∨ p1)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_568116855405465900741282355 : ((((p1 ∧ (((((p3 ∧ p4) ∧ False) → (p5 ∨ p4)) ∨ (((((p3 ∨ True) → p1) → p2) → False) → p2)) ∨ False)) ∧ p1) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47041321496753280896743107385 : (((((p5 ∨ ((p5 ∧ (p2 ∨ (p5 ∧ (False ∧ p2)))) ∧ p1)) ∧ (p5 ∧ ((p3 ∨ p1) ∧ (p4 ∨ False)))) ∧ (True ∨ p1)) ∨ (False → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257400964994431222547121607067 : ((p2 ∨ p5) → ((p4 ∧ p4) ∨ (((False ∧ (p2 ∧ (p3 ∧ (p2 ∧ ((True → p1) ∨ (True ∨ (p4 ∨ p4))))))) ∧ p5) ∨ (True ∨ (p5 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65784542548716845632338636727 : ((p4 ∨ ((True → ((False ∨ (False ∧ False)) ∨ ((False → p3) ∧ ((p2 ∧ p1) ∨ True)))) → (((p3 ∧ p4) → p5) → (p4 ∧ (False → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



