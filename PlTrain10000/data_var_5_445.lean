variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226568496946005689066473460649 : (((p4 → p3) ∨ False) ∨ ((p2 → (True → (((((p2 ∨ p3) → (p5 → ((p5 ∧ (p3 ∧ p5)) → False))) ∨ (p1 ∧ p2)) ∨ True) ∨ True))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115225621988233268342698175161 : (((((False ∧ (p4 ∧ False)) ∧ (True ∨ (p3 ∧ p3))) ∧ p5) ∨ (((p5 ∨ p4) → (p3 → False)) ∨ (False ∨ (p1 ∨ (p3 ∧ True))))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258496309648796082707180849432 : ((p5 ∨ p2) → ((True → False) → (p1 ∧ ((p4 ∨ (((True ∧ p1) ∨ (p2 ∧ (((p4 → False) → p5) ∧ p3))) ∧ ((True ∨ p2) ∧ p4))) ∨ p3)))) := by
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
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h13
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48789442065003164161188048210 : (((True ∧ ((p5 ∨ True) → ((p5 ∨ (((p3 ∧ ((p1 ∧ (p3 ∨ p5)) ∨ p2)) ∧ p4) ∧ (p4 → p3))) ∧ True))) ∧ (p4 ∨ (p4 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245241384184481786973382133324 : ((p2 ∧ p1) ∨ ((((p5 ∧ p1) ∧ p3) ∨ (False ∧ ((p2 → (p1 → (p2 → False))) ∧ (p1 → p4)))) → (((p4 ∧ True) → (False ∧ False)) ∨ p1))) := by
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
    let h5 := h3.left
    let h6 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350134163259099551829581633204 : (p4 → (((p1 ∧ ((((p2 ∨ p3) ∨ p2) ∨ p1) ∨ (((p3 ∧ p5) → p4) ∧ p4))) ∨ ((((p1 → (p3 ∧ p4)) ∨ p4) → p2) ∨ True)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730022970817138652426792523294 : (((((False ∨ p2) → p1) → (p3 → (p1 ∨ (True ∧ (((((((p5 → False) → p2) ∧ p2) ∨ (p1 ∧ (False ∧ p2))) ∧ p2) ∧ True) → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644808261030177686697758325683 : ((((p2 ∨ (((p1 → ((p3 ∨ (p5 ∧ (p3 ∨ (p4 → False)))) ∨ (p2 ∧ False))) ∨ (p4 → (False ∧ ((p5 → p4) ∨ p5)))) → p2)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746929081765921129217160352817 : ((((p4 ∨ p1) → ((False ∨ (p5 ∨ ((p5 → (True ∧ (p2 → (p1 → (p1 ∨ (p3 ∧ (((True ∧ p1) ∨ p2) → p1))))))) ∧ False))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762524219067731630226634415617 : (((p3 ∧ (((p3 ∨ (p4 ∨ p1)) → ((((p2 ∨ (p5 → p4)) ∧ (p2 ∨ p4)) ∨ p3) ∨ False)) ∧ (((p1 ∨ False) → (False ∧ p1)) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66846051379523974499979726709 : ((True → (p4 → ((((((False → (p1 → p4)) ∧ (True ∨ p2)) → ((p2 → (p3 ∧ p4)) ∧ True)) ∨ (p1 ∨ p3)) ∨ (p1 → p4)) ∨ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254897070382549138721813450175 : ((p4 ∧ True) → ((p1 → ((((p3 → ((p4 ∨ True) ∨ p3)) ∨ p1) → (False ∧ False)) ∨ (True ∧ p1))) ∨ (p5 → (p4 ∨ (True ∨ (True ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668573891054214932483782655108 : ((((((p1 → False) ∧ (((True ∧ p4) ∧ (p4 ∨ (p1 ∧ ((p2 → p1) ∧ True)))) ∧ ((p5 ∨ p1) → p2))) ∧ p4) ∨ ((p3 ∧ p2) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_51882632779007182841627748509 : (((((((True → p5) ∨ (p1 → (p2 → False))) ∧ ((p1 ∧ p2) ∨ p4)) ∨ p3) → False) ∨ (((p4 ∨ (True ∧ True)) → p2) ∧ (p4 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123390419820866842118890475879 : (((((p5 → ((p2 ∧ p2) ∧ True)) ∧ (((False → True) ∧ (p5 ∧ (p2 → p2))) → p3)) ∨ p1) → (p3 ∧ (p3 ∨ (p3 ∨ p3)))) → (p2 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158190759947918071149972356118 : (((p2 → (True ∨ (p2 ∧ p3))) → (((p5 → p3) → (p1 ∨ p2)) ∧ (((True → p5) ∨ p2) ∨ p1))) ∨ (((p5 ∨ p2) ∧ False) → (p1 ∧ True))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308335786574594955483176930116 : (p2 ∨ (((((p1 → ((p3 → p3) → (True ∧ ((p4 ∧ True) ∧ ((False ∨ (True ∧ (p5 ∧ p4))) ∧ p3))))) ∨ (False → p5)) → p2) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58525922863454185122613792127 : (((p5 ∨ p1) ∧ ((p4 ∧ (p2 ∨ (((False ∨ p3) ∧ (p1 ∧ True)) → p4))) ∧ (p1 → (((p5 ∨ False) ∧ p3) ∨ (p2 ∧ (p4 ∧ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38458476984729948787415500075 : (((((False ∨ ((p5 → p4) ∨ (p2 ∨ (True ∨ p5)))) → ((True → True) ∨ True)) → (p5 ∧ (p2 ∧ (p5 → ((p5 ∨ p4) → p2))))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348799313418657398804608803457 : (p3 → (p1 ∨ ((((p1 ∨ False) ∨ ((p5 → p1) ∨ (((False → p3) ∨ (False ∨ ((p2 → (p3 ∧ True)) ∨ False))) → p4))) ∧ p1) ∨ (False → True)))) := by
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
theorem thm_5_vars_83352929351401406664065299606 : ((((True → p3) ∧ ((p4 → ((((p1 ∧ (False ∨ p5)) ∨ False) → p3) → p2)) → (False ∧ p3))) ∧ ((((p3 ∧ True) ∨ p5) → p2) ∧ p4)) → p5) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h8 : (p4 → ((((p1 ∧ (False ∨ p5)) ∨ False) → p3) → p2)) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h11 : ((p3 ∧ True) ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h13 := h4 h12
      -- One of the premise coincides with the conclusion.
      exact h13
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h14 := h6 h11
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h15 := h5 h8
  -- We need to get the left conjuct of h15 based on <expert-advice>.
  let h16 := h15.left
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204703340185722916113960701009 : (((p4 ∨ (p3 ∧ (p5 ∧ p2))) ∨ p4) ∨ (((((p3 ∧ False) → ((p1 ∨ (((p3 ∧ (True ∧ True)) ∧ True) ∧ p4)) ∧ p4)) ∧ p4) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53818609204885237064096018711 : (((((p1 ∧ (p3 → (p4 ∨ False))) ∧ p3) ∨ (p1 ∧ p5)) ∨ (((p2 ∨ (((p4 ∨ (p1 → (p5 → p2))) ∧ p2) ∨ p1)) → True) ∨ p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322440436348569779710783769911 : (p5 ∨ ((((p5 ∧ False) ∨ (p4 ∨ p5)) ∧ (p2 ∨ ((p3 → (p3 ∧ ((((p1 ∨ (p4 → True)) → p5) → (p3 → p5)) ∧ p2))) ∧ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719805099209772480320209881647 : ((((p2 → (p1 ∧ (p3 → p3))) ∨ (p1 ∨ ((p2 ∧ (False ∨ (((p2 ∨ p4) ∨ ((True ∨ p5) ∧ (p2 ∨ p2))) ∨ p3))) ∧ (p1 → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159034063761332681644733265910 : ((p4 ∨ (p2 ∨ ((p1 ∨ (((p3 ∧ (((p3 ∨ (p2 ∧ True)) ∨ p4) ∧ p1)) ∨ p4) ∧ p4)) ∨ p1))) ∨ (p2 ∨ ((False → p1) ∨ (p4 ∧ p3)))) := by
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
theorem thm_5_vars_166550956692805738881455740932 : ((p5 ∨ ((((p3 ∧ p2) ∨ True) ∨ (p1 ∨ (p1 → p4))) → (p3 ∨ ((p4 ∨ p5) ∨ True)))) ∨ ((p5 ∧ (False → False)) → (p5 → (True ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133865762445093512564683854043 : (((p2 ∧ (p5 ∧ (p3 ∨ (p1 → (p5 ∧ ((False ∧ p5) ∧ ((p1 ∧ (p3 ∧ ((False ∨ False) ∧ True))) → p5))))))) ∧ p4) ∨ (p2 → (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112221229455996596457185989115 : (((p1 ∨ (((p1 ∧ (p3 ∨ (p1 → True))) ∨ ((p1 ∧ p3) → ((p1 → p2) ∨ (p2 ∧ p3)))) → ((p2 ∧ p1) ∨ p5))) ∨ p5) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326129599608816112625807062935 : (p5 ∨ (p1 → ((p4 ∨ (p3 ∨ p3)) → ((p2 ∧ False) ∨ ((p2 ∨ ((True → p2) → (p4 ∨ ((p4 → ((False → p3) → p1)) ∨ p5)))) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165440206734281232233256332206 : (((p1 → ((p2 → ((p2 ∨ ((p2 ∨ True) → p3)) → False)) → p5)) → (True ∧ (p2 ∨ p2))) ∨ ((p5 → (p3 ∧ (p5 → (p5 ∧ p2)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144559640487480762678233410258 : (((((p2 ∨ p1) → p1) ∨ ((True ∧ (p5 ∨ ((False → ((p3 → p4) ∧ False)) ∧ True))) → p1)) ∨ (p3 → True)) ∧ (p1 ∨ (True ∨ (p1 ∨ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157261289193250738812383245556 : ((((p1 → (p4 ∧ (p5 ∨ p5))) ∨ ((p5 ∨ True) ∨ (p5 ∨ (((p4 → p1) → p5) ∨ p3)))) → p3) ∨ ((((p4 ∨ True) → p1) → p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337348172880690955766283283778 : (p1 → (((p1 → ((((False ∨ p3) ∧ p2) ∨ p3) ∧ ((((p3 → p2) ∨ (p3 → (p2 ∧ p2))) → False) ∧ p3))) ∨ p2) ∨ (False → (True → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356363551676938030286671279249 : (p5 → ((p4 ∧ ((((p4 → p1) → p2) → (p2 ∧ p4)) → (p3 ∨ (p3 ∨ p1)))) ∨ ((False ∧ (p3 → p1)) → (p1 ∨ (p1 → (False → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53214238206394555956529943928 : (((((False ∨ p4) ∨ ((p1 ∧ p3) ∨ p2)) ∨ ((False ∨ p1) → True)) ∨ ((((p4 ∧ True) → (False → (p5 ∨ (p3 ∨ True)))) ∨ p3) ∨ p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41140842110648508103310073355 : ((((((((p1 ∨ p5) ∨ (p1 ∧ True)) ∧ ((p5 ∨ (p2 ∨ p4)) ∨ False)) ∧ p2) → ((p5 ∧ p1) → False)) ∨ (True ∨ (p3 → True))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165869384035544188734312422680 : (((p2 → (p1 ∧ p3)) ∨ ((True → p2) → ((((p3 → p1) ∨ False) ∨ (p3 ∧ p1)) ∨ p4))) ∨ (False → ((False ∨ False) → ((True ∧ True) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58050680668175444707064574275 : (((False ∧ False) ∧ (p4 → (((p3 ∨ p2) → ((p4 ∧ ((p1 ∨ p2) ∧ ((p3 ∨ (p4 ∧ False)) → p5))) → False)) ∨ ((p1 ∧ p5) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166444597280194910065704283131 : ((p2 ∨ ((p5 → (p3 ∧ ((True ∨ p5) ∨ ((p3 ∧ (False → p4)) → (p5 → p5))))) ∨ p1)) ∨ (p4 → ((p1 ∧ (p5 → p2)) ∨ (p4 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53215438350659557130487161966 : ((((p3 ∨ ((False ∧ p3) ∧ (p3 → True))) ∨ (p1 ∨ (p3 → p5))) ∨ ((False ∨ p1) ∨ ((((False → True) ∨ (False → p4)) ∨ p2) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190204065833012326027941687981 : (((p5 ∨ (((p3 → (p1 ∨ p5)) ∧ p5) ∧ p5)) ∧ p3) ∨ (((p3 → p5) ∧ p3) ∨ (False → (((p5 ∧ p4) ∨ (p4 → p1)) ∨ (p4 → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791130981538297158663506227633 : (((True → (((p1 ∧ ((((p5 → p2) ∧ p1) ∨ p3) ∨ p3)) → (p2 → ((p1 → ((False → p1) → p2)) → ((False ∨ p4) ∧ p2)))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172981431779215065234332616612 : ((p4 ∧ (p5 ∨ (p1 ∨ (p5 → ((True ∧ p1) → ((p4 ∧ (p4 ∨ p4)) ∨ p1)))))) ∨ (p4 ∨ (p3 → (p4 ∨ (p3 ∨ (True ∨ (p4 ∨ p1))))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194695675637061510766093252534 : ((((True ∧ p5) ∨ (True ∨ (p3 → False))) ∨ p4) ∧ ((p5 ∨ p4) → (((p1 ∨ p3) ∧ p3) ∨ (False → (((p4 ∧ (False → p5)) ∨ p2) → p2))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h3
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h3
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22437788961764266001622420122 : (((False ∨ (((p4 → (False → False)) ∨ p2) ∨ p2)) → (((p5 ∧ (False ∧ p1)) → p1) ∧ (((p1 ∨ (p2 ∨ p2)) ∧ p3) ∨ (p4 → True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
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
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158270088745733341462968535083 : (((p1 ∨ (p1 → p2)) ∨ (p2 → ((((False ∧ p5) ∧ p1) ∨ (False ∨ ((True ∧ p3) → True))) ∨ False))) ∨ (p4 ∧ (((p1 → p3) ∨ p1) ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608323064289212741948512224149 : ((((((((p2 ∧ (True → False)) → (False → True)) → ((((False ∧ True) ∧ ((False → (p2 → p3)) ∨ p3)) ∧ p1) ∧ True)) ∨ True) ∨ False) ∨ p1) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_352676516483544090159986783558 : (p4 → ((p1 ∨ p5) ∨ ((((((False ∨ ((p2 ∨ p4) ∧ (p4 → (True ∧ (p2 ∧ (p5 ∧ False)))))) ∧ p3) ∨ p3) → (p1 ∨ p4)) ∨ True) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775393352563877458686261515837 : (((False ∨ (p1 ∧ (True → ((True → p1) ∧ (p1 ∨ ((False ∧ p5) ∨ (((p3 ∧ p5) → (p1 → p5)) ∧ (((p5 ∨ False) ∧ p4) ∨ True)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157044940976521596527988007230 : (((False ∧ ((p5 → True) ∧ ((False ∧ (((p1 ∧ p4) ∧ p2) ∧ (True ∨ p1))) ∨ (p1 ∨ p5)))) ∨ p3) ∨ (False ∨ ((True ∨ True) ∨ (False ∨ p2)))) := by
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
theorem thm_5_vars_102139294096635352793850607881 : (((((True ∧ ((True → (True ∨ (p3 → (p5 → p4)))) → (p5 ∧ p5))) → p3) ∨ ((((False → p5) → p3) ∨ p2) ∨ True)) ∧ True) ∧ (p5 → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64109743037185411013016481402 : ((False ∨ (((p5 ∧ (((p4 ∧ False) → False) → p1)) → False) → (p1 ∧ (p2 ∧ (False ∨ ((p1 → ((p3 ∨ p2) ∧ p3)) ∧ (p1 ∨ p2))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185713161029435744840309474155 : ((p2 → ((p4 ∧ p2) ∧ (((p1 → p2) ∧ p5) → (p3 → p4)))) ∨ ((p4 → ((p5 ∧ (p5 ∨ (False ∨ True))) → (p2 ∨ False))) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345488221770835319823158237754 : (p3 → ((((((False ∧ False) ∨ p1) ∧ (p4 → p2)) → (((False ∧ (p3 ∧ p2)) ∧ (p2 → False)) ∧ p5)) ∨ (p4 → (p3 ∧ (False → p4)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42696928063489712825916526094 : (((p5 ∨ ((((((p5 ∨ p4) ∧ p4) ∧ True) ∧ ((False ∧ p1) → p5)) ∧ (p3 ∨ ((True ∨ p3) → p3))) ∧ (p2 → (p5 ∨ p1)))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55137734783293959079496168376 : ((((p5 → ((p2 → p2) ∧ False)) ∧ p4) ∨ (p3 → (((True ∧ (((p5 ∨ False) ∧ p2) ∨ (p2 ∧ (p5 ∨ p3)))) ∨ p2) ∨ (False → False)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619164251331439192264403603057 : (((((p3 ∨ (False ∨ p3)) ∨ ((p3 → (p5 → (True ∨ p2))) ∧ ((False → ((((True → p1) → p5) → p4) ∨ (p4 → p5))) → p5))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196896302867946047997734498377 : (((p3 → (p3 ∧ (p5 → (False ∨ p5)))) ∧ p2) ∨ (True → (p3 ∨ (p1 → (True → (((p5 → p4) ∧ p4) → ((p1 → p2) ∨ (p4 ∨ p2)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315731955273940879555536801408 : (p3 ∨ ((p1 → p5) ∨ (((p1 → (p1 → p1)) → False) ∨ ((p1 → (p1 ∧ ((p4 ∨ (p5 → p4)) → True))) ∨ ((p4 ∨ False) ∧ (p1 ∧ p2)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301953220807921704680292536998 : (False ∨ ((p4 ∨ True) → (((((p1 → (((((p1 ∨ p4) ∨ True) ∧ p4) ∧ (p3 ∧ p2)) → (True ∧ p2))) ∧ p3) ∨ p2) ∨ (p2 → True)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_202213725876959651858453327710 : (((False ∧ ((True → p3) → p2)) → p1) ∧ ((((p3 ∨ False) → ((p5 ∨ (p3 ∧ (p1 → False))) → p1)) ∧ ((p2 → True) ∨ p4)) ∨ (p4 ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184650683379558150447481349804 : (((((p1 → p4) ∧ (p3 ∨ False)) ∨ False) ∨ (p5 ∧ (p2 ∧ p5))) ∨ (p5 → (((p1 → p5) ∧ (p3 → (p2 → ((True → p2) ∨ p5)))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138395050150570887440202203487 : ((p4 → (p3 ∨ (((p1 ∧ p1) ∨ p4) ∧ ((p1 ∧ p2) ∨ (p1 → (p4 ∧ (p4 ∨ ((False ∧ (p3 ∧ p3)) ∧ p3)))))))) ∨ ((p4 → False) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632549462294983650094467541283 : (((((p5 ∨ (True → ((False ∨ (p3 ∧ p2)) ∨ ((p1 → (p3 → ((p2 → True) ∨ ((p5 ∧ (p4 ∧ p4)) ∨ True)))) → True)))) → False) → p2) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ (True → ((False ∨ (p3 ∧ p2)) ∨ ((p1 → (p3 → ((p2 → True) ∨ ((p5 ∧ (p4 ∧ p4)) ∨ True)))) → True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150503811848847601202850099497 : (((((((p3 → (p1 → p5)) → (((p2 ∧ True) ∨ p5) → p4)) → p3) ∧ p5) → ((p4 ∨ p1) → p5)) ∧ p2) → (((p5 → p1) ∧ p5) ∨ True)) := by
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
theorem thm_5_vars_791945611975472469285589298242 : (((True → ((p1 ∧ ((((p5 ∧ ((p5 ∨ True) ∨ (False ∧ True))) ∨ False) → False) ∧ (True ∨ (p3 → (True ∨ (p4 → False)))))) ∨ (p1 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303745571708093726144945064494 : (p1 ∨ (((((((p2 → p5) ∨ p5) ∨ p2) ∧ ((p5 ∨ (True ∧ p5)) ∨ (((p1 ∨ (p2 → (p2 ∧ p5))) ∨ p4) ∧ p1))) ∧ True) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66165558090677253405465555063 : ((p5 ∨ ((((((True ∧ p3) ∨ p1) ∧ (p4 → (p2 → ((p3 ∧ p2) ∧ (p5 → p2))))) ∧ p3) ∧ (p3 ∨ p3)) ∨ ((False ∨ False) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329765347282711862663607327694 : (True → (True ∧ ((p2 → (p2 ∧ ((False → ((p4 ∨ (p2 → p4)) → p4)) ∧ ((True ∨ p2) → (p5 ∨ (p4 ∧ p3)))))) ∨ (True → (True ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341987490744124033468812640102 : (p2 → ((((p4 ∨ p3) ∧ ((((p2 ∨ p2) ∧ True) ∨ (p5 → (p2 → p4))) → p5)) ∨ ((True ∨ p5) → (True ∨ False))) ∨ (p5 ∧ (p3 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323187468728838168978514664327 : (p5 ∨ ((((p1 ∧ (((p5 ∨ ((((True ∨ p2) ∨ p1) ∧ (p1 ∨ True)) → (p5 ∨ p2))) ∨ p5) ∨ (p3 ∧ p2))) ∧ p1) → p2) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111708971828034707188497098894 : ((((((p4 → False) ∨ ((p1 → (p5 → True)) ∨ (p3 → ((p5 ∧ p3) ∧ p4)))) ∧ ((p1 ∨ False) → (p5 ∨ p3))) → False) ∨ True) ∨ (p2 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56025839247070547975365572697 : ((((p1 ∧ (p3 → p5)) ∨ p3) ∨ ((((((p4 ∧ p2) → p1) ∧ False) ∧ p3) ∨ ((p3 ∧ p4) → True)) ∨ ((False → (p5 → p2)) → False))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_683647277361068556640896380771 : ((((((((p1 ∧ p3) → False) → p5) ∧ (((p3 → (False → p1)) ∧ (p5 ∨ p4)) ∨ False)) ∧ p2) ∨ ((True ∨ (False ∨ p1)) ∨ (False → p5))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_138406586577322596190345734644 : ((p5 → ((((p4 ∨ ((p1 ∧ (p3 ∨ True)) ∧ p5)) ∨ False) → (((p1 ∧ (True → p2)) ∨ (p3 ∨ p2)) → p4)) ∧ p2)) ∨ (p5 ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119122332041971351265520920542 : ((p1 → (p1 ∧ (p1 → (((True → ((p1 → p1) ∧ p5)) ∧ ((p3 ∨ p4) → False)) → ((p2 ∨ (p1 ∧ (p4 → False))) → p5))))) ∨ (p1 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
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
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h17 := h14 h16
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600177489317352158242986797198 : (((((False → True) → (p1 ∧ (((True ∧ (p2 → (False ∨ p1))) ∧ p4) ∧ ((False → p2) ∧ ((p3 → True) ∨ ((False → True) ∧ p3)))))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_894600789811919606041895907505 : ((((True → ((((p2 → True) ∧ ((False → False) ∧ False)) ∧ ((p4 ∧ ((True → (p5 ∧ p3)) ∨ True)) ∧ p4)) ∧ p4)) ∧ (False → (p3 → p1))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158353167727352883620989387575 : (((True ∨ p1) ∧ ((False → p1) → ((((False ∨ p3) ∨ p2) ∨ p2) → (p5 ∨ (p1 ∨ (p5 ∧ p2)))))) ∨ ((p4 ∧ False) → ((p2 ∧ True) ∨ p1))) := by
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
theorem thm_5_vars_356562922208996818702895817267 : (p5 → (((p1 → (True ∧ (False ∧ p1))) → ((p2 → p1) → False)) → (((p2 ∧ ((False ∧ p3) ∧ p5)) ∧ p2) ∨ ((p2 → (p1 → p3)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190530711478447349031054549964 : ((((p1 ∨ ((p2 → (p3 ∧ p2)) ∧ p2)) → p2) → p2) ∨ ((p1 ∨ p4) → (((((False ∧ p3) ∨ False) ∨ False) ∨ True) ∨ ((p1 ∨ p5) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_261061483341171382139000300720 : ((p4 → p2) → (p2 → ((p4 ∨ (False ∧ (p5 ∨ ((p5 ∨ (p4 ∧ (True ∨ True))) → (True → p1))))) ∨ (p2 ∨ (((p1 → p2) → p2) → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219008887284008526704961282419 : ((p4 ∧ (True → (p2 ∨ False))) → ((((((p3 ∨ (((p4 ∧ p4) ∧ False) → p2)) → False) ∨ ((p5 → p2) ∧ (p4 ∨ p5))) ∨ p5) → p3) ∨ True)) := by
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
theorem thm_5_vars_27046882727487522703077564010 : (((True → p4) ∨ (((False → (p5 → p1)) ∨ (((p4 ∧ p5) ∨ (False ∨ (p2 ∧ (p1 ∨ (False → p2))))) ∨ p4)) → ((p1 ∨ True) ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- False on the left can always be used.
          apply False.elim h9
        case inr h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337855478647316068543408479320 : (p1 → ((((p1 ∨ ((p2 → p2) ∧ True)) ∧ (p4 ∧ (True ∧ (p3 ∨ True)))) → p2) ∨ (False → (p5 → (p2 ∧ (p1 ∨ (p5 ∧ (p4 ∧ p4)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168419475685702677417148483141 : (((p4 ∧ p3) → (((p1 ∨ (p3 ∨ (p4 ∨ (p4 ∧ False)))) ∧ False) ∨ (p4 → (p5 ∧ False)))) → (((p5 ∨ (p2 ∧ (False ∧ p5))) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46869986922170632165768958381 : ((((True → ((p3 ∨ (False ∧ ((True → p2) ∧ (((p1 ∨ (p3 → (False → p4))) ∨ p2) ∨ p4)))) ∧ (p5 ∨ p1))) ∧ p4) ∨ (p4 → p4)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314406629354435009687740552249 : (p3 ∨ (((((p5 → ((p2 → p3) → False)) → False) → (((False ∨ (False ∧ p5)) ∨ (p2 ∨ True)) → p3)) ∨ p5) ∨ ((p5 → (p5 ∨ p2)) ∨ p1))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_565568112805905209510547016987 : (((True → (((p1 ∨ ((True → (False ∨ False)) → (p3 → (((False ∨ p5) ∨ (p3 → p5)) → (False ∧ True))))) → p4) ∨ ((False ∧ p1) → p5))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115334794414183083013864946270 : (((p5 ∧ ((True ∨ p2) → (((p5 → p2) → p1) ∧ p1))) → ((((True ∧ False) ∧ (p1 ∨ p3)) → (p4 ∨ True)) → (p1 ∨ p5))) ∨ (p1 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161049379847348315368794503762 : ((((False → False) → False) → ((True → p4) → ((p1 ∨ ((p5 ∧ (False ∧ p5)) → p5)) → (p5 ∨ p5)))) → ((p5 → True) ∧ ((p5 → p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175118657187069912128950079341 : ((p4 ∧ (p1 ∧ (((p5 ∧ p3) → (((p5 ∧ (p2 ∧ False)) ∧ p2) ∧ True)) ∧ p1))) → ((p1 ∨ p1) → ((p2 ∧ p5) ∨ (p2 → (p3 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h19
    -- Implications on the right can always be decomposed.
    intro h20
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133262442099052055677659824613 : ((p2 → ((True ∧ (p2 → ((((False → p5) → p4) ∧ ((p1 → (True ∧ False)) ∧ (p3 → (p2 ∨ p2)))) ∨ p4))) → p4)) ∧ (p5 → (p5 ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h12 : (False → p5) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h13
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h14 := h8 h12
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- One of the premise coincides with the conclusion.
    exact h15
  -- Implications on the right can always be decomposed.
  intro h16
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680917883453790058886265375941 : (((((p4 ∨ p4) ∧ (((((p2 → False) → False) ∧ (p5 ∧ (p4 ∧ ((p1 → p5) → p3)))) ∧ p4) ∧ p1)) → (p5 → ((False ∧ p4) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41002685368930990850726206777 : ((((((((p1 ∧ p3) → (((p5 → (p4 ∧ ((False ∧ p5) ∧ (p2 ∧ p2)))) → p5) ∨ p3)) ∨ False) ∧ p4) ∧ p5) → (p2 → p2)) ∨ p2) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187220199513631186666316776790 : (((p1 → p5) → (((False → p2) ∨ (True → (True ∧ p5))) ∨ p3)) → (((((p2 ∨ p4) ∨ p5) ∨ True) ∧ (p2 ∧ (p2 ∨ (True ∧ False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166036091349359219866052259965 : (((p2 → p3) ∨ ((((p1 → p3) → (p5 ∧ p1)) → (p1 ∨ (True ∧ p3))) → (p3 ∨ True))) ∨ (p5 → ((p5 ∨ (p3 → (p2 ∨ p2))) → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118193524280723712282873724334 : ((False ∨ (p5 ∨ (((((p1 ∨ ((p3 → p1) → p1)) → p4) → ((False ∨ (((p5 → p3) ∧ p5) → True)) ∨ p4)) → p3) ∧ p4))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46642474061214697352602034070 : (((p5 ∧ (True ∧ ((True ∨ p1) → (p5 → (p2 ∨ (((p5 → (((p2 ∧ False) ∨ True) → (p2 ∨ p4))) → False) ∨ p2)))))) ∧ (p1 → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



