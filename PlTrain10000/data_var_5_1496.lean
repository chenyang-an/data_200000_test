variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136499044698673910008240574011 : ((((p1 → p4) → p3) ∧ (((p2 ∨ p3) → ((p5 → True) ∧ p1)) ∨ (p1 ∨ ((True ∧ (p5 ∨ p1)) ∧ (True ∨ True))))) ∨ (p1 ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350201225136943086188672591565 : (p4 → (((p5 ∨ (p5 ∧ p5)) ∨ (((((((p4 → p4) ∨ False) → (p1 → (p2 ∨ p2))) ∧ p5) ∨ (p1 ∨ p1)) ∧ p3) ∨ (p1 ∨ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654025108521000211018193721355 : (((((p2 ∨ (((False ∨ ((((p5 ∨ (p3 → p2)) ∧ False) ∨ True) ∨ p3)) ∧ p3) ∧ (True → ((p1 ∨ False) → p4)))) ∧ p2) ∨ (p1 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209447573032195304078300786787 : ((p2 → (p3 ∨ (p4 ∨ (p3 ∨ True)))) → (((True ∨ True) → (False ∧ ((p4 ∧ p1) → (((p3 ∧ p4) ∨ False) ∨ p2)))) → ((p5 ∨ p2) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (True ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678159594227339580689329796849 : (((((((p4 ∧ p4) ∨ (True ∧ (((p5 → p2) → p5) ∨ p2))) ∨ p3) → ((False ∧ (p4 ∧ p1)) ∨ True)) ∨ (True ∨ ((p1 ∨ p3) → p2))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_64014046563076243528072563074 : ((False ∨ ((((p1 ∧ (p3 ∧ ((p3 ∨ p4) ∨ p2))) ∧ (True ∧ ((False ∨ (p1 ∨ p2)) ∨ False))) ∧ (p1 ∨ (False ∧ p4))) ∨ (True ∨ p1))) ∨ p3) := by
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
theorem thm_5_vars_149135382488963702119474809203 : (((p4 ∧ p2) ∧ ((p3 ∨ (p2 ∧ (False ∨ (p3 → (False → ((p3 ∧ ((p5 ∨ True) ∧ p2)) ∨ p1)))))) ∨ p1)) ∨ (False ∨ (p4 → (p5 ∨ True)))) := by
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
theorem thm_5_vars_164548512491932203492617928604 : ((((True ∧ (((False → p4) → (p2 ∨ False)) → True)) → (((False ∨ True) ∨ False) ∧ p4)) ∧ p5) ∨ (p1 → (((p3 ∧ True) ∨ (p4 → True)) → p1))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9172268171516409074940673009 : ((((((p3 ∨ (p2 ∧ (p5 ∨ False))) ∧ (p4 ∨ True)) ∨ p1) ∨ (p5 ∨ (False → ((((p4 ∨ (p5 ∨ p1)) → False) → p4) ∨ p5)))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_10169496563014167384201453915 : (((p1 ∨ ((((p1 ∨ p3) → (p3 ∨ p3)) ∧ ((True ∨ p5) ∧ ((p3 → p1) ∧ (p3 ∨ (p1 ∧ (True → (p4 ∧ True))))))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788962076497829381209606874316 : (((p5 ∨ (((p2 ∨ True) ∧ ((p5 → False) ∨ ((False ∨ (p1 ∧ ((False → p1) ∨ p2))) ∧ (True ∧ ((True → False) ∧ True))))) ∨ (True ∨ p3))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_166733365314089735737203268354 : ((p4 → ((p1 → (p3 ∨ ((((((p2 ∧ True) → p5) ∨ True) ∧ p3) ∧ True) ∧ False))) ∧ p4)) ∨ ((((p3 ∨ (p4 ∧ p2)) → p1) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157385033323373261127049194856 : ((((((p3 → p1) ∨ (((p1 ∨ p1) ∨ False) ∧ (p3 ∧ (False ∨ p1)))) ∨ False) ∨ p3) ∧ (False → p1)) ∨ (True ∧ (((p2 ∧ False) → p1) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56560735409207546527127824854 : (((p4 ∨ (True → (True → p1))) → (((p4 ∨ (((p1 → False) → p4) ∨ p1)) → ((p3 ∨ p2) ∧ (p2 → False))) ∧ (p1 ∨ (True ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159230594482587275959535257397 : ((p3 → (((((True ∨ p5) ∧ ((p4 ∨ (p2 ∨ False)) ∨ (p1 → False))) ∧ (p4 ∧ p3)) ∨ False) ∨ True)) ∨ (p2 ∨ (p5 ∧ ((p5 ∧ False) → True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748635970586936381625766522243 : ((((p3 → p2) → ((p2 → ((p3 ∨ (p4 ∨ True)) ∧ (p4 → p4))) → ((p5 ∨ (((p1 ∨ p4) ∧ False) ∧ p1)) ∧ ((p2 → False) → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124223719415981514185504315479 : (((((True ∨ True) → (((p2 ∨ p4) → p3) ∨ p5)) ∨ True) → ((p4 → ((p4 ∨ p2) ∧ ((p5 → (p4 → p2)) ∨ False))) ∧ False)) → (p2 ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True ∨ True) → (((p2 ∨ p4) → p3) ∨ p5)) ∨ True) := by
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
theorem thm_5_vars_256864469078825422564857937438 : ((p1 ∨ p3) → (p1 ∨ (((p2 ∧ p3) ∨ ((p4 ∧ (((p1 ∨ (True ∨ p3)) → p4) ∨ ((p5 ∧ (p1 → p4)) → False))) ∨ (True ∧ True))) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616445183072562604981549100604 : ((((((p1 ∧ (False → ((p1 → p3) → p4))) ∧ ((False ∨ True) ∧ p2)) → ((False → (p4 ∧ p2)) ∧ (((True → p2) → False) ∨ False))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57248636206765737008493872285 : ((((p4 ∧ p1) → p5) ∨ (p4 ∨ ((True → (((p5 ∧ p3) ∨ p1) → True)) → (((p2 → False) ∨ True) ∨ (True ∨ ((p5 → True) → p2)))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217562032204962152697511588870 : ((((p4 ∧ p1) ∨ p3) → p1) → (((((p3 ∨ p1) ∧ ((((False ∧ p2) → (p4 → True)) ∧ p5) → p4)) ∨ p1) → (p4 ∨ (p4 → p1))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : ((p4 ∧ p1) ∨ p3) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h8
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157824894035073852398921837678 : ((((p3 → p2) ∧ (False → ((True ∧ p1) ∨ (p1 → (p2 ∨ p1))))) → ((p2 ∧ p2) ∧ (p3 ∧ p3))) ∨ (((p3 → p3) ∧ p2) → (p2 ∨ p5))) := by
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
theorem thm_5_vars_340752751897913565558542231367 : (p2 → (((((p3 ∧ p1) → True) → ((((True → (p4 ∨ p4)) → p3) ∨ p4) ∨ (False ∨ (p2 → ((p5 ∨ (True ∨ p2)) ∧ p2))))) ∨ p5) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215341264981404174236270232075 : ((p1 ∧ (p1 → (False ∧ False))) ∨ ((p5 → ((p4 ∨ ((p1 ∧ (((p3 ∨ p1) ∨ False) ∧ p4)) → True)) → (((False ∨ p1) → p1) ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721927186773779634308688123208 : ((((p5 ∨ (p1 ∨ (p2 → False))) → (((((((p4 ∧ True) ∨ p5) ∨ p5) ∨ p1) ∧ True) → (p2 → ((True ∧ p5) → False))) ∨ (True ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322389657561997741510545746723 : (p5 ∨ (((True ∨ (((False ∨ (p4 → p3)) → (p4 ∨ ((False ∧ (p4 ∧ p3)) ∧ p2))) ∨ True)) → ((p5 ∧ ((p1 ∧ p5) ∨ p1)) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38883953963605334359095446147 : (((((True ∧ p4) ∨ p1) ∨ (p3 → (p4 ∨ ((p5 ∨ ((((p5 ∧ (p2 ∨ False)) → p3) → (True → (p3 ∨ p3))) ∨ p1)) → p2)))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241317101914849096854886340268 : ((False → True) ∧ (False ∨ (((p4 → ((True → (p3 ∧ ((p2 ∨ p3) ∧ (p3 ∨ True)))) ∨ False)) → p4) ∨ ((p4 → p1) ∨ (p2 ∨ (False → p4)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51374622403972507178866359074 : (((((((p1 → (p2 ∧ (((p3 ∧ p5) ∧ p4) ∧ p2))) ∧ p4) ∨ (p3 ∧ False)) ∨ p5) ∨ False) → ((p3 ∨ False) → ((True ∧ False) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614242299919139236892669305736 : ((((((p1 ∧ ((p5 → (p5 ∨ ((True → False) ∧ p2))) ∨ (p3 ∨ (p3 ∨ (True ∧ p4))))) → (p1 ∧ p1)) → ((True → p3) ∧ p4)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350351187918060724180812810303 : (p4 → ((p4 → ((p1 ∨ ((((False ∨ (p3 → p5)) → p1) ∨ (False → p3)) → p1)) ∨ ((((p5 → (p2 → p5)) ∧ p4) ∧ p4) ∨ p5))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137316046467501783484032882612 : ((p2 ∧ (((p1 ∧ (p4 ∨ p3)) ∧ False) ∧ ((True ∧ p4) ∨ (False ∧ ((p1 ∨ False) → (p2 ∨ (p2 → (p5 ∧ p3)))))))) ∨ (False → (p1 ∧ p5))) := by
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
theorem thm_5_vars_213329325089349811775028488418 : (((p1 ∧ (False → p3)) ∧ p1) ∨ (((p5 ∧ ((p1 ∧ (p4 ∧ ((p5 ∨ p2) → (p4 ∧ p3)))) ∨ (p5 ∨ (True ∨ p5)))) ∨ True) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185222483991398082344777802186 : ((False ∧ ((((p1 ∨ p2) → ((p1 ∨ p3) → p5)) ∨ p5) → p3)) ∨ (((p1 → ((False → p2) ∨ (((True → p5) → p3) ∧ p2))) → False) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → ((False → p2) ∨ (((True → p5) → p3) ∧ p2))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804164706330170917022166799427 : (((p3 → ((p2 ∨ ((p2 ∨ ((p4 ∨ ((True ∧ p5) → ((p3 ∧ p3) → True))) → p4)) ∧ (p2 ∨ True))) → ((p4 ∨ (p2 ∧ p3)) ∨ p3))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
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
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40380557780367981450182875417 : (((((p2 ∨ (((((p2 ∨ (p1 ∧ (p5 ∨ (p2 ∨ p5)))) ∨ p3) ∨ ((p2 ∧ p3) → False)) ∧ p2) → p1)) ∧ (p3 ∧ p1)) ∨ p5) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655523814904046010440444067064 : (((((((True ∨ ((True ∨ p5) → (p3 ∨ p2))) ∧ ((p3 → p2) ∧ ((p5 ∨ p2) ∨ (p3 → True)))) → p1) → (p3 ∨ p1)) ∨ (p3 → p3)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66187661227467464937372926806 : ((p5 ∨ (((False ∧ (p1 → (p5 ∧ p2))) → ((p3 → p2) ∧ (p4 ∧ (True ∨ (p5 ∧ (False → p3)))))) → (((p5 ∧ False) → p3) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747686101055737775885243769668 : ((((False → True) → ((p3 → ((((p2 ∨ p1) ∨ False) → ((p5 ∧ ((p3 ∨ p3) → (p2 → False))) → True)) → p1)) → ((p1 ∨ p3) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116794409074732263865675212230 : (((p2 ∨ p1) ∨ (((((p2 ∧ (p2 ∧ p4)) ∨ p4) → (p1 ∧ (p4 ∨ (p4 ∨ (False ∨ p1))))) → p4) → (p1 → (False ∨ p4)))) ∨ (p4 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p2 ∧ (p2 ∧ p4)) ∨ p4) → (p1 ∧ (p4 ∨ (p4 ∨ (False ∨ p1))))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h17 := h1 h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219113889600279630772733697916 : ((True ∨ ((p4 ∨ p2) → p3)) → (((p5 → False) ∧ p2) ∨ (p2 ∨ ((p2 → p3) → (((((p3 ∧ False) ∧ p1) ∧ (True → p3)) ∧ p5) → p2))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165834846241807194476120801729 : ((((p4 ∧ p4) ∧ p5) ∨ (((p1 ∨ p4) ∨ p5) ∧ (((p1 ∧ p4) ∧ (p5 → p2)) → p1))) ∨ (p5 → (True ∧ (p2 → ((False ∨ p1) → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111037092921333029095572217539 : ((((p4 ∧ ((((p5 ∨ (p4 ∧ (p4 → False))) ∧ (p3 ∧ True)) ∨ (p3 ∧ False)) ∨ True)) ∧ (p1 → ((False → p5) ∧ p4))) ∧ p1) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114060317335946901461276924259 : ((((((((p5 ∧ (True → p1)) → p1) ∨ p3) → p3) ∨ False) ∧ ((((p3 → p5) ∧ p5) ∨ False) ∨ p2)) ∨ (False → (p1 ∧ False))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115116335675045706526499370175 : ((((((p1 ∨ ((p3 ∨ p2) ∨ p2)) ∧ p1) → False) ∧ (True → p2)) → (((True ∨ p2) → p5) ∨ (((p4 ∧ False) ∧ p4) → True))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259028526247907691348910307046 : ((True → p4) → ((p1 ∨ ((False → (p5 ∧ ((p1 ∧ (p5 ∧ p5)) ∨ p2))) → (p4 ∧ p1))) → (p2 ∨ ((p3 ∨ (False ∧ (p5 ∧ True))) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (False → (p5 ∧ ((p1 ∧ (p5 ∧ p5)) ∨ p2))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h6
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593108258305624444403314081480 : ((((((False → (((p3 ∧ p1) ∨ (p1 ∧ ((p3 ∨ False) ∧ (p4 ∧ (p5 ∨ p2))))) ∧ False)) → (p1 ∧ False)) ∨ (False ∧ (p5 ∧ True))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351528880972605974962208405183 : (p4 → (((p3 ∨ (((True ∨ ((((p2 ∨ p4) ∧ p3) ∨ p4) ∨ p5)) → p3) ∨ p1)) → (p5 ∨ p3)) ∨ (((p1 → p2) ∧ (p2 → p5)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113658918267184694348324394469 : ((((p1 → (((((p4 → True) ∧ ((((p5 ∧ False) ∨ False) ∨ p3) ∨ p4)) → (True ∨ False)) ∨ p4) → p1)) ∧ p3) → (p5 ∧ p3)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118417981347536698470050889591 : ((p2 ∨ (p4 ∧ (((True → (True ∧ p2)) → p1) → ((((((p4 ∧ p1) ∨ (True ∨ (p4 ∨ p4))) ∧ True) ∨ p3) ∧ p5) ∧ p2)))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692091182490903135086262235861 : (((((True ∧ (((((p1 → False) ∨ (p4 ∧ p3)) ∨ p5) → p2) → False)) ∧ p3) ∧ (((p3 → ((False ∧ False) ∨ (False ∧ p5))) ∧ p2) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321311111205324450310108931062 : (p4 ∨ (p5 ∨ (((True ∨ (((((p3 ∧ False) → p2) ∨ p1) ∧ (False ∧ ((p4 ∨ p3) ∧ True))) ∧ p2)) → p1) → (p5 ∨ ((p1 ∨ p5) ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115973781083671341262321703886 : ((((False → (False ∧ p4)) ∧ p5) → (((True ∧ (((True ∧ p4) → p1) ∨ (p2 ∧ ((p1 ∨ True) → p3)))) ∨ p2) ∨ (p5 ∧ p5))) ∨ (p4 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198626481795652720384450865780 : ((p3 ∨ ((((True ∧ p5) ∧ p2) ∨ p2) ∧ p4)) ∨ ((True ∨ ((p3 ∧ p2) → (True ∨ ((p1 → p2) → p4)))) → ((True ∨ (p5 → p4)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758366786450801536636531444366 : (((p2 ∧ (((((p4 → p5) ∧ True) ∧ ((p1 → ((p4 → (False ∨ (p4 → p2))) ∨ p1)) → p4)) ∨ (True ∨ (p3 ∨ (p3 → p1)))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20838230464422173462465716092 : ((((p3 ∨ (((False → p1) ∨ p2) → (p2 ∧ p1))) ∨ (p2 ∧ p1)) ∨ ((True ∧ p2) → (((p2 → (False ∧ (p5 ∨ p5))) → p3) → p2))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251011813566967521501690240648 : ((p1 → p5) ∨ ((p3 → ((p1 → p3) → (p2 → ((((p5 → p1) ∨ False) ∨ p5) ∧ False)))) ∨ (((p3 ∨ False) ∧ True) → ((p4 → p3) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44060911530053188304219852677 : (((((((p2 ∧ p3) → ((False ∨ (p1 → (p4 → p2))) ∨ (p4 ∧ (p2 → p5)))) ∧ (p1 ∨ p3)) ∨ False) ∧ ((p3 ∨ p4) → False)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309782938710065294377833590744 : (p2 ∨ (((((p2 ∨ ((p2 ∨ p4) ∨ p1)) ∧ (((False → p4) ∨ p4) ∨ p4)) ∧ (True → (p2 → True))) ∨ True) ∨ ((p3 → False) ∧ (p4 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733917625915728060042148184986 : ((((True ∨ True) ∧ (((p3 ∧ p1) ∧ p1) ∨ (False ∧ (p1 ∨ (((True → ((False ∨ p5) ∧ (p2 ∧ (p2 ∨ p2)))) ∨ False) → (p3 → p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_73887863296007386739950787029 : ((((False ∨ (((p4 ∨ False) → (p1 ∨ False)) ∧ (True → p1))) ∧ ((p5 ∨ (p4 → p4)) ∧ (p3 → ((p5 ∧ True) → (False ∧ p4))))) ∨ False) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h4.left
      let h10 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h12 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h13 := h8 h12
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h15 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h16 := h8 h15
        -- One of the premise coincides with the conclusion.
        exact h16
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695219063932850804547896450468 : (((((p4 → (((p3 → ((p4 ∨ p5) ∨ (p1 ∧ p5))) → p2) ∧ p4)) ∨ p5) → (p4 ∨ ((((False ∧ (False ∨ False)) ∧ p4) → p5) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16015526770398733820836157795 : (((True → ((p5 → (((((False → p2) ∨ (p4 ∧ ((p5 ∧ p1) → (p2 ∧ False)))) → (p3 ∧ p2)) → p2) ∨ p1)) ∧ p1)) → (p1 ∨ p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_624726061162222627915786038644 : ((((p4 ∨ (p1 → (p3 ∨ ((((p3 ∧ ((p2 ∧ (p2 → p2)) ∧ (p3 ∧ ((p3 → False) ∧ p1)))) ∨ p4) ∨ p5) ∧ (p2 ∨ p2))))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40703487602090608703223652595 : ((((((False → (((False ∨ ((p2 ∨ p4) ∧ p3)) → p2) → p1)) → p2) ∨ (p1 ∧ (p1 → ((True ∧ p3) ∧ (p2 → p2))))) → p4) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47415130201932401730742285351 : (((False ∧ (False ∨ ((p2 → (False ∨ (p2 → (False → p1)))) → ((True → ((p4 ∧ ((p5 → p4) → False)) ∧ p4)) ∨ p2)))) ∨ (p3 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650515005811572319253678408167 : (((((((True → (p2 → True)) → (True ∧ ((p2 → p1) ∨ p2))) ∨ p2) ∨ (p1 → ((p5 ∧ (p5 ∨ (True ∧ p3))) → p5))) ∧ (True ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137403945256896765583496211888 : ((p3 ∧ (p4 ∨ (((p4 → (p5 ∧ p4)) ∧ ((p3 ∨ p5) → p2)) ∨ ((p3 ∨ (p2 ∨ ((p4 → p1) → False))) ∨ True)))) ∨ ((True ∨ p2) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117031282418446951790349215487 : (((p2 ∨ p4) → (p1 ∨ (((True ∧ ((p2 → ((p5 → p2) → (p1 ∧ p1))) ∨ True)) ∨ False) → (p4 ∧ ((p4 ∨ p2) ∧ False))))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118261918315962043306009279666 : ((p1 ∨ (((p4 ∨ ((False → (p2 ∧ False)) ∨ (p3 ∨ (p3 ∧ p4)))) ∧ p3) ∨ (p3 ∨ ((True → False) → ((p5 ∨ p4) ∨ p1))))) ∨ (p4 ∨ p5)) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349979270895565336068178111624 : (p4 → (((((((p3 ∧ ((p1 ∨ p1) ∨ p1)) ∧ (True ∧ (p5 → (p5 ∧ p2)))) → True) → (((True ∨ p5) ∧ False) ∧ p3)) ∨ True) ∨ p4) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57124586451293571497200888192 : ((((p5 ∨ p3) ∧ p3) ∨ ((p5 → ((((p5 → p4) → (True → ((False ∧ p2) ∧ p2))) → (p3 ∧ p2)) ∧ (True ∨ p1))) ∨ (False ∨ True))) ∨ False) := by
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
theorem thm_5_vars_214619761979763881773437223961 : (((True → p4) ∧ (p1 → p5)) ∨ ((((p1 ∨ (((p1 ∧ (p5 ∧ p3)) → p1) → (p1 → (p2 ∨ p2)))) ∨ False) ∨ False) ∨ (False → (p2 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787963773092442118043520376077 : (((p4 ∨ (p4 → (p3 ∨ (((p5 ∨ (p3 ∨ ((p3 → (True ∨ p4)) ∨ p5))) → (p5 ∧ (((p3 → p2) ∨ p5) ∨ p3))) ∨ (False ∨ True))))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123230980989457086718027185438 : ((((((((p1 → (p4 ∧ p3)) ∨ p5) ∨ True) ∨ p3) → p2) ∨ (((p1 ∧ p1) ∨ True) ∧ p3)) ∧ (p5 → (p2 ∨ (p5 → True)))) → (p3 ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175232269080124720182605091969 : ((p1 ∨ ((p5 → ((p2 ∧ p4) → False)) ∧ (False ∨ (p1 ∨ ((p2 ∨ True) ∧ p4))))) → (((p1 ∧ (p5 ∧ (p1 ∨ p1))) ∨ True) ∨ (p3 ∧ False))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114732749989481842594182844527 : ((((((True → (p3 ∨ p2)) ∧ True) ∨ p2) → ((((p4 → True) ∧ False) ∧ p1) ∧ p2)) → (p2 ∧ ((True → (p4 ∧ p4)) ∧ p2))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204360659339415474720898551811 : (((p2 ∨ ((p3 ∨ p3) ∧ p4)) ∧ p2) ∨ (((p1 ∧ p3) ∨ True) ∨ ((((True ∧ False) ∧ p2) → ((p4 → (True → False)) ∧ (p4 ∨ p1))) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48664711146421710277042072513 : ((((((p5 ∨ ((p1 → (p1 → p1)) ∧ p5)) ∧ True) ∨ (p4 → False)) ∨ (p5 ∧ ((False ∧ p3) ∨ (p3 ∨ p5)))) ∧ ((p3 → p4) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168789455972222523616437897848 : ((p1 ∨ (p5 ∨ (((False ∨ p5) → (((p5 ∨ True) ∧ True) → (p3 ∨ (False ∧ p3)))) → False))) → ((p2 ∧ (p2 ∨ (True ∨ p4))) ∨ (True ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111803674350951251602493067158 : (((((p4 → (((p2 ∨ ((p5 ∨ (True ∨ (p4 ∧ p3))) → ((p1 ∧ p4) → p2))) ∨ p5) ∨ p4)) → False) → (p4 ∨ p2)) ∨ p4) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63346868488105701931454500296 : ((p5 ∧ (False ∧ ((p4 ∨ (p5 → p5)) → (p5 → (((False ∨ (p3 ∧ (p3 → ((p1 → p1) → False)))) ∨ ((p3 ∨ p5) → p5)) → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647800983468729884570320774832 : ((((((((((False ∧ p4) ∧ p1) ∧ (False → p4)) ∧ p3) ∨ ((((p5 → p2) ∨ True) ∧ (p1 ∧ p2)) ∨ p4)) ∧ True) ∧ p1) ∧ (p1 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715178018012645417466575083108 : ((((True → (p1 ∧ ((p4 → False) ∧ p2))) → ((True ∧ (((p3 ∨ (p5 ∧ (False ∧ p3))) ∧ True) → ((p1 → (p4 → p2)) → p2))) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_219363559003791685168372855665 : ((p3 ∨ ((p4 ∧ False) ∨ p3)) → (p4 ∨ (((((True ∧ p4) ∨ p1) ∧ (False → p4)) → ((p3 → p2) → (False ∨ (p1 ∨ (p4 ∨ p1))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57953134015977204563101338481 : (((p1 → (False → p1)) → ((p2 ∨ ((p4 ∧ p1) → (((p5 → p2) ∧ ((p2 ∧ p5) ∨ ((True ∨ p5) → p1))) ∧ True))) ∨ (p1 → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192695521422547944764602677349 : ((((p2 → (False ∧ (p2 → p1))) ∨ (False → p2)) → False) → ((((False ∨ True) ∨ p2) → (((p3 ∨ p5) ∨ (False → p2)) ∧ False)) ∧ (True ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h12 : ((p2 → (False ∧ (p2 → p1))) ∨ (False → p2)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- False on the left can always be used.
        apply False.elim h13
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h14 := h1 h12
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h16 : ((p2 → (False ∧ (p2 → p1))) ∨ (False → p2)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- False on the left can always be used.
      apply False.elim h17
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h18 := h1 h16
    -- False on the left can always be used.
    apply False.elim h18
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h19 : ((p2 → (False ∧ (p2 → p1))) ∨ (False → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h20
    -- False on the left can always be used.
    apply False.elim h20
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h21 := h1 h19
  -- False on the left can always be used.
  apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49165758774645591945871475749 : ((((((p1 ∨ p4) ∨ False) ∧ (True → False)) ∨ (((p2 ∧ ((False ∨ (p2 → p5)) ∧ p2)) ∧ p3) → (False ∨ p5))) ∨ ((p4 → True) ∧ p2)) ∨ p4) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612512962830565274711361498881 : ((((((((p4 → ((True ∧ ((p1 → p2) ∧ ((p1 ∨ p5) ∨ p5))) ∧ p5)) → p2) → ((p1 ∨ p5) ∧ False)) ∨ p3) ∨ (p3 → False)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_48404089478759096702914662949 : (((p1 → ((p5 ∧ (p5 → (False → p3))) ∧ ((p1 ∨ p3) → (((p4 ∨ p3) ∧ (p2 → p4)) ∨ (False ∨ (p1 ∨ p4)))))) → (False ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801701328844779646120197822595 : (((p2 → (((p1 ∨ False) ∧ p5) ∧ ((((True → (p4 ∧ (p4 ∨ p3))) ∧ (((p5 ∧ p4) → False) ∨ (p2 → (p1 → p3)))) → p1) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343001284974411814574649334954 : (p2 → ((p1 ∨ ((p1 ∧ p5) ∨ p4)) ∨ ((p3 ∧ (((p2 → p1) → p1) → p1)) → (p2 ∧ ((p5 → p5) → (((p5 ∨ False) ∨ p2) ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116500978099056153665114646949 : (((p3 ∧ p4) ∧ ((((((True ∧ (p5 → (p2 ∨ p4))) ∨ p4) ∨ p5) ∨ ((False ∨ p2) ∧ (p5 → p1))) ∨ (p2 ∨ p1)) ∧ p5)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753080568291048379000946488 : (((p4 ∨ (p3 ∧ p5)) ∨ (((p1 ∨ p5) ∧ p2) ∧ ((p5 ∨ (((True ∧ (p5 ∨ p3)) ∧ p4) ∧ p3)) ∧ (False → (p1 ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192504280976259564841082486370 : ((((p2 ∨ p5) ∧ (p4 → (False ∧ (p3 ∧ False)))) ∨ p4) → (((p1 ∨ (True → ((p4 → p2) ∨ (False → ((p2 ∧ p2) ∧ p3))))) ∧ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h11 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h12 := h4 h11
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- False on the left can always be used.
      apply False.elim h13
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h16
    -- False on the left can always be used.
    apply False.elim h16
    -- False on the left can always be used.
    apply False.elim h16
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59581108221606236077518144495 : (((p4 → False) ∨ ((((p3 ∧ (p5 ∨ p5)) → False) ∧ ((p2 ∧ (True ∨ ((((True ∧ False) ∨ p4) ∧ (p4 ∧ False)) ∨ True))) ∧ p1)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52021290991519947402298355839 : (((False ∨ (((p3 → p1) ∨ ((p4 ∨ p5) ∧ ((p1 ∨ (False ∧ p2)) ∧ p4))) ∨ p1)) ∨ (p1 ∨ ((True → p3) → (p4 → (True ∨ p3))))) ∨ False) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171517598564598381822886622547 : ((((p1 ∧ ((p4 ∨ (((p4 → p4) → False) → False)) → (p2 → p2))) ∧ p1) ∨ p2) ∨ ((((True ∧ (True → True)) ∨ p3) ∧ False) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254223760114289529313885535688 : ((p2 ∧ p2) → ((((p5 ∨ ((p3 ∧ (False ∨ False)) ∨ (p3 → p1))) ∧ ((p3 ∨ p1) ∨ (p5 → p1))) ∨ (p1 → True)) ∧ (p2 ∨ (p1 → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353405655523135064055673455469 : (p4 → (p1 ∨ (((p3 ∧ (True ∧ ((p5 → p1) ∨ (p3 ∧ (p3 → (p4 → ((((p2 ∧ True) → True) → p1) → False))))))) ∨ (p4 ∨ False)) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



