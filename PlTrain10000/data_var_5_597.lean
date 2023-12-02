variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587990829592525582358861922679 : ((((((True → ((((p3 ∧ ((p3 → ((True ∧ True) ∨ p2)) ∧ p1)) ∨ p4) ∨ (True ∨ p3)) → p5)) → ((p3 → p1) ∧ p4)) ∨ False) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2464742397442217688384135205 : (((p2 ∨ False) ∧ (((p2 ∨ p1) ∨ True) → (False ∧ p2))) ∨ (((False ∧ True) ∨ (False → p4)) ∨ (p3 ∨ (((p4 ∧ False) → p1) → False)))) := by
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
theorem thm_5_vars_313236789982049718991423207774 : (p3 ∨ (((p1 ∧ p5) ∨ (True ∧ (p5 ∨ (((p5 ∨ (((False ∨ True) → p3) → p2)) ∧ (p4 ∨ ((p3 ∨ (False ∨ p1)) ∨ p2))) ∨ p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115417254843155557860831320350 : (((((((True ∧ p4) → p2) ∨ p2) → p4) ∧ p4) ∨ ((p3 ∧ p2) ∨ ((((((False ∨ True) → p2) ∧ p5) ∧ True) ∨ True) ∧ False))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595161307496509104735583929198 : (((((((p4 ∨ ((p1 → True) → (p3 ∧ p3))) ∨ (p3 ∧ False)) → (True ∧ False)) → ((((p1 ∨ p4) ∧ (p3 ∨ p2)) ∧ p2) ∨ True)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227449866028462673605957859186 : (((p5 → p5) → p5) ∨ ((True → ((((False ∨ (p2 ∧ False)) ∨ (True ∨ ((p4 → ((p3 ∧ p1) ∨ False)) ∨ (p1 ∧ p3)))) ∧ p3) ∧ False)) → p1)) := by
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314751146402483757492722585042 : (p3 ∨ (((p1 ∧ p5) ∧ ((p5 ∧ p1) ∨ (((True ∧ p4) ∧ (True ∧ p3)) ∨ p1))) ∨ (((((p3 ∨ (p5 ∨ p1)) → p4) ∧ p4) ∧ p2) → p2))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310449948266946097827018751712 : (p2 ∨ (((((p1 ∧ p4) ∧ True) ∨ True) ∨ p4) ∧ (((((True → (p5 → True)) ∧ p2) → p3) → (p3 ∧ True)) → ((p3 ∨ (p5 ∨ True)) ∨ True)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50359627125491090448227114355 : (((((p5 ∧ p2) ∧ True) ∧ (p2 → (((((p5 ∧ p1) ∨ p5) ∧ False) ∨ ((True → p5) ∧ False)) → p4))) ∨ ((p3 ∨ (p1 → False)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241396405509234450834899518104 : ((False → p1) ∧ (((True ∨ ((False → ((p2 → (p1 → False)) → True)) ∨ True)) → ((((p5 → (p2 ∧ (True ∧ False))) → True) ∧ p2) ∨ False)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40830636489749586275879333760 : ((((p1 → ((((True ∧ (((p4 ∨ p1) ∨ (True ∧ p3)) → (((p5 ∧ p2) ∨ (p1 ∨ True)) ∧ p2))) ∨ p4) ∨ p3) → p3)) → p3) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197970757776874847350176454496 : (((False ∨ False) ∧ (((True → p4) ∨ False) ∨ False)) ∨ (((p5 → (p5 → p2)) → ((p3 → p2) → p3)) ∨ ((p5 ∨ (p3 ∨ (True ∨ True))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_355097291596567117078031853900 : (p5 → (((True → ((p1 ∨ ((((((p1 → p4) → (((p5 ∨ p3) ∧ p4) ∨ p4)) → (p4 → p1)) ∧ p5) ∧ p1) ∧ p5)) ∨ True)) → p2) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True → ((p1 ∨ ((((((p1 → p4) → (((p5 ∨ p3) ∧ p4) ∨ p4)) → (p4 → p1)) ∧ p5) ∧ p1) ∧ p5)) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159393331852547116034517734651 : ((((((False → p4) → (p5 ∧ (((p2 → p3) ∨ (p2 ∨ (p3 ∧ True))) ∧ p5))) ∨ False) → p5) ∧ p2) → (p3 ∨ ((p3 → p1) ∨ (True ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147177445153223493576293321222 : (((p1 ∨ ((p3 ∧ False) ∨ (True ∧ (((p4 ∨ (p4 ∨ p5)) → True) → (True ∧ (p2 → (p5 ∨ p5))))))) ∧ True) ∨ ((True ∨ p5) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64446567143871201261571969251 : ((p1 ∨ ((((p2 ∨ (p3 ∨ (True ∧ (p2 ∧ ((p1 ∨ False) ∨ True))))) ∧ ((p2 → (p4 ∧ p4)) ∧ (False ∨ p4))) ∧ p2) → (p5 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37498027505407789705932901067 : (((((p5 → (p4 → p1)) → (((False ∧ p1) ∧ p3) ∨ ((p5 ∧ (p4 → ((p1 ∧ p1) ∨ ((True ∨ p3) ∧ p3)))) ∧ p3))) ∨ p2) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_6197308065312506666128757782 : (((((p2 ∧ ((False ∨ p5) ∧ ((p3 → p2) ∧ p4))) ∨ p5) ∨ ((False ∨ ((True ∨ (True ∧ p5)) ∧ (p1 → (p1 → p1)))) → True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_888910785096753918683797260298 : ((((((p5 → (True ∧ p4)) → ((True → p4) ∨ p2)) ∨ (p1 → ((p1 ∨ (p3 ∨ (p2 ∧ False))) ∧ ((p4 ∨ p5) ∨ p1)))) → (True ∧ False)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 → (True ∧ p4)) → ((True → p4) ∨ p2)) ∨ (p1 → ((p1 ∨ (p3 ∨ (p2 ∧ False))) ∧ ((p4 ∨ p5) ∨ p1)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148329131901121198023048319185 : (((((((p2 → ((p3 ∨ p3) ∨ False)) ∧ False) ∧ (p4 ∧ p1)) ∨ False) ∨ p4) ∧ (((False → p2) → p5) ∨ True)) ∨ (False → ((True → p3) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205572593907087445896946048040 : (((False → p3) ∧ ((p5 → p2) → p3)) ∨ ((p5 ∧ True) → (p4 ∨ (((((False ∨ p2) ∧ p1) ∨ (((p3 ∨ p3) ∨ p3) → True)) ∨ p2) ∨ p2)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747676625843626291243063266403 : ((((False → True) → ((p1 ∧ ((((((((p4 ∧ p1) ∧ False) → (True → p1)) → (p5 → p3)) → p2) ∨ (p5 ∧ False)) ∨ p5) → p5)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305609624510523388003724776051 : (p1 ∨ ((((p2 → (p4 ∨ (p3 ∨ p1))) ∨ ((False ∧ True) ∧ p5)) ∨ False) → (p3 → ((p3 ∨ p1) → (True → ((False ∨ p2) ∨ (p1 → p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
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
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h20.left
        let h23 := h20.right
        -- False on the left can always be used.
        apply False.elim h22
    case inr h24 =>
      -- False on the left can always be used.
      apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303930103570028944431162946969 : (p1 ∨ ((((((p5 ∧ True) ∧ False) ∨ p5) ∨ (p5 ∧ False)) ∨ ((True → ((p1 → (True ∧ False)) → (((p4 → p3) ∧ False) ∧ p3))) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358488523244013701120088874906 : (p5 → (p1 → (((p3 ∨ p5) ∧ True) ∧ ((p3 ∨ ((p1 → ((True ∧ ((False ∨ (p5 → p2)) ∨ p4)) ∧ p3)) ∨ p3)) ∨ (p3 → (p4 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51937677523889336576205091911 : (((((p5 ∧ (((p4 → p4) → p4) ∨ p5)) ∧ p4) ∨ ((True ∨ p3) ∨ (p1 ∨ p4))) ∨ (True ∧ ((p3 ∨ (p4 ∨ (p1 ∨ p3))) ∧ p4))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337363523009726952886257952265 : (p1 → ((((p3 → (p5 → (p2 ∨ (p2 ∨ (p2 ∨ True))))) ∧ (p4 ∨ (False ∨ True))) ∧ ((True ∨ (p5 ∨ p3)) ∨ p1)) ∨ ((p4 → p1) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226015537223892288070835556142 : (((p4 ∧ p2) ∨ p4) ∨ (True ∧ (p3 ∨ ((False ∨ ((p5 → (((p3 ∨ False) ∧ ((True ∨ p5) → False)) → False)) ∨ (p4 ∧ True))) ∨ (True ∧ p5))))) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (True ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617607115071283005720108015252 : (((((p3 → ((False ∧ (p3 ∧ True)) ∧ p3)) ∧ (True → ((p2 → ((p3 ∨ p4) ∨ ((p1 ∧ ((p4 → p3) ∨ p1)) ∨ p4))) ∨ False))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778342198468412161730270302143 : (((p1 ∨ (p1 ∧ ((((((False → p1) → (p2 ∧ (p3 ∨ p1))) ∨ p5) ∨ p4) ∨ ((True ∧ (True ∧ ((p3 ∧ p1) ∨ p2))) ∨ False)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157074546510905920917787509842 : (((p1 ∨ (p2 ∨ ((False ∨ p4) ∧ (p3 ∨ (((p5 ∧ p3) ∨ (p3 ∨ True)) → (False ∨ p3)))))) ∨ p3) ∨ (p2 → (((p3 ∨ False) ∨ True) ∨ False))) := by
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
theorem thm_5_vars_356925039530898303114590708763 : (p5 → ((p3 → ((True ∨ p1) ∧ p3)) → ((((p4 → ((False ∧ ((False → False) → False)) → ((p3 → False) ∨ p1))) → p4) ∨ p2) ∨ (False → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727121258820572245871906606781 : ((((True ∧ (p3 ∧ p3)) ∨ ((((p3 → (False → p1)) ∧ p4) ∧ (((p2 ∧ p4) ∧ (False → p1)) ∧ (p5 ∧ (p5 ∧ (p5 ∧ p1))))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133915031458360020234761589998 : (((p3 ∨ (True ∧ ((p4 → ((p3 → p3) → (((p5 ∨ p5) ∧ p1) ∨ (False ∧ ((p4 → p2) ∨ p4))))) ∨ p5))) ∧ False) ∨ ((True ∨ p5) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689152763030903104572254043274 : ((((((((((True ∧ p4) ∨ ((p4 → p3) ∨ False)) ∧ p4) ∨ p4) ∨ p5) → p5) → p2) ∨ (((True ∧ (p5 ∨ (p1 → False))) ∨ p2) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299326178840627674316271234460 : (False ∨ (((p4 ∧ (p2 ∧ (p4 ∨ p3))) ∧ (p5 ∧ ((((p3 → (p4 ∨ False)) ∧ (p5 → (False → ((p1 → False) → p1)))) ∨ False) ∧ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619443596296227257591414410872 : (((((True ∨ (p2 → p4)) → (False ∧ (p5 → ((p4 ∨ ((True → p5) ∨ p3)) ∧ (p3 ∨ (((p3 → p1) → (p2 ∨ p4)) ∨ True)))))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_229099755910876171780460587418 : ((p5 ∨ (p5 → p1)) ∨ (((p5 ∨ p1) ∧ (((p3 ∨ (p4 ∨ p3)) ∧ p1) → (p4 ∧ (((True ∨ (p5 ∧ p2)) → (p2 ∨ True)) ∧ True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186429666035859318308158972308 : (((False → (p3 → ((p5 → (True ∨ p4)) → (p5 → p3)))) → p2) → ((((p4 ∨ p3) ∨ False) ∧ ((True → ((True ∨ p4) ∧ p3)) ∨ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326170719443472601933851748598 : (p5 ∨ (p2 → (((p1 ∧ ((p4 ∨ False) ∨ False)) ∨ (((True ∧ p4) ∨ ((p5 → (p5 ∧ p4)) ∧ (p4 → (False ∧ p5)))) → p1)) ∨ (False → p3)))) := by
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
theorem thm_5_vars_191550251014131466695659548988 : ((p1 ∧ ((p5 → p3) ∧ ((False ∧ p2) ∨ (p2 ∧ False)))) ∨ ((p5 ∧ p3) → ((p5 → p2) → ((True ∧ p1) → ((p1 ∨ (False ∧ p5)) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119582610401453749140416550586 : ((p5 → ((p4 ∨ p5) ∧ (((p2 ∨ (False → p4)) ∧ ((False ∨ ((False ∧ p1) ∧ ((False ∨ False) ∧ (p2 → p2)))) ∨ True)) ∧ True))) ∨ (p4 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157595360910225256320778604169 : (((p5 ∨ (((p4 → ((False ∨ p2) → (p3 → p4))) ∧ (p5 → (True ∧ p4))) → p3)) → (p5 → p3)) ∨ (((p5 ∨ p3) ∨ True) ∨ (p1 ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69201863211375040824209221706 : ((p5 → (((p4 → ((False ∧ p1) ∧ (p5 ∨ False))) ∨ (p2 ∧ True)) → ((True → ((p3 ∧ (((p4 ∨ True) ∧ True) ∧ False)) ∧ p5)) → False))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h13
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803248294532399610853229778948 : (((p3 → ((((p3 → ((False → (p4 → (p5 ∨ ((p1 → p1) ∧ (False ∧ (p5 → (p5 ∧ p2))))))) → False)) ∨ p5) ∨ (p3 ∨ p5)) ∨ p1)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147500642362219270395037797626 : (((False ∨ (p5 ∧ ((((((p5 ∨ (p1 ∧ p1)) → p5) ∧ p4) ∨ (True → (False ∨ False))) ∧ p1) ∨ p4))) ∨ True) ∨ ((True → p5) → (p3 → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45233857425816496709904997757 : (((p1 ∧ ((((p1 ∧ p4) ∧ (((p4 ∨ p3) ∨ (False ∧ (((p1 → True) ∧ False) ∧ (p3 ∨ p2)))) ∨ p2)) ∨ (True ∧ False)) → p4)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173098327765676034485375043371 : ((p1 ∨ (p5 ∧ (((p4 → p4) → False) ∨ (p5 → (p2 ∧ (p4 → (p4 ∨ p5))))))) ∨ (((p1 → (True ∨ False)) ∨ p1) → (False → (p3 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165209190915599322899036730590 : ((((((p1 ∨ p1) ∧ ((p4 → (True → True)) ∧ p3)) ∧ p2) ∧ (p5 → p3)) ∨ (p3 ∧ p4)) ∨ (((p1 ∨ (p3 ∨ False)) ∧ True) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305991018219570317879416158379 : (p1 ∨ (((p5 ∧ (p4 ∨ p2)) ∨ p1) ∨ ((p5 ∨ (((((p5 → p5) ∧ p4) ∧ ((p5 ∨ p3) → (p2 → p1))) → p2) ∨ p1)) ∨ (p4 ∨ True)))) := by
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
theorem thm_5_vars_40789023477522443250426908448 : ((((p3 ∧ (p3 ∨ ((p3 → ((p3 ∨ (p3 ∨ ((p2 → p4) ∨ p4))) ∨ p4)) ∨ (((p3 ∧ p1) ∧ (p1 ∧ p4)) → p5)))) → p2) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196706972955093958527171993243 : ((((p5 → (p2 ∧ (True → p4))) ∨ p1) ∧ p5) ∨ ((((p5 ∧ True) ∨ (True → (((p3 → p2) ∨ True) → ((p2 → p3) ∧ p5)))) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336242618452556496636437015684 : (p1 → ((((p1 ∨ p1) ∧ (((p2 ∨ p3) ∨ (((p4 ∨ (p2 ∨ (p5 → False))) → p2) ∨ True)) → p2)) ∨ (p3 ∨ ((p4 → p1) ∨ p3))) ∨ p2)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146392001555821753868270513065 : ((p2 ∨ (((((p2 ∧ p4) ∧ (p2 ∨ ((p1 ∧ False) ∨ p2))) ∧ (((p1 → p3) ∨ p2) ∧ p1)) ∨ p4) ∨ True)) ∧ ((p3 ∨ (False → p1)) ∨ False)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117894667287567676960345732540 : ((p5 ∧ (((((p4 → ((p1 ∨ p4) ∨ True)) → True) → ((False ∨ ((True ∧ p3) → p5)) → p3)) → p4) ∧ ((True ∧ False) → p3))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75814668513894090794640263298 : (((((p2 ∨ p5) ∧ (False ∧ (((p1 ∨ ((p4 ∨ p3) ∨ ((p3 ∧ (True ∧ False)) ∨ True))) ∧ ((p4 ∧ p1) → p3)) → False))) ∨ True) → p3) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∨ p5) ∧ (False ∧ (((p1 ∨ ((p4 ∨ p3) ∨ ((p3 ∧ (True ∧ False)) ∨ True))) ∧ ((p4 ∧ p1) → p3)) → False))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245997634356819191852675523138 : ((p4 ∧ True) ∨ (p5 ∨ (p2 ∨ (((p1 ∨ ((p2 → p3) → (p5 → (True ∨ p2)))) → p2) ∨ ((((p2 ∧ p2) ∧ p4) ∧ (p1 ∨ True)) → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328419021509138962768777667924 : (True → ((((((p3 ∨ p4) ∧ p2) ∧ p5) → False) ∨ (p3 ∨ (((p5 → (p4 ∧ p2)) ∧ True) ∧ p5))) ∨ (((p5 ∨ True) ∨ (p4 → p2)) ∨ p2))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112520727209865615476153546340 : ((((((((True → True) → (False ∧ (False ∧ False))) ∧ (p2 ∧ (p3 ∨ (False → p5)))) ∨ ((p4 → p4) → p5)) → False) → p3) → p1) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179870507190319057473606451488 : (((p3 → (True ∨ ((True ∨ (False ∨ True)) ∧ (p5 ∨ (p4 ∨ p1))))) ∧ p1) → (((p5 ∨ (p4 ∧ True)) ∨ (p4 → ((p5 → False) → p2))) ∨ p1)) := by
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
theorem thm_5_vars_303323598784977606275247831317 : (p1 ∨ (((((((p1 ∨ p3) ∨ ((p3 ∨ True) ∧ (((p2 ∨ False) → p1) → p5))) ∧ False) ∧ ((True → p5) ∨ (p1 ∨ p3))) ∨ True) ∨ p2) ∧ True)) := by
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
theorem thm_5_vars_117015027408680873923212848568 : (((p1 ∨ p1) → (((True ∧ ((True ∨ p1) ∧ (p1 ∧ p4))) → p1) → (p5 → (((p1 ∧ ((p1 ∧ p3) ∧ p3)) → False) ∧ True)))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67553442217828833839772532300 : ((p1 → ((p4 ∧ (p5 → p1)) → (((True → p5) ∧ (p5 ∨ ((p2 ∨ ((False ∧ p2) → (p3 ∧ ((p5 ∨ False) → p5)))) ∧ p4))) → p5))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h2.left
    let h8 := h2.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h2.left
      let h14 := h2.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h16 := h4 h15
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h2.left
      let h19 := h2.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h20 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h21 := h4 h20
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662232664153692644831982125641 : ((((((p1 → ((p4 ∧ (p3 ∧ (p5 ∨ p5))) ∨ p2)) → p3) ∨ ((((False ∨ p4) → (p3 ∨ p3)) ∧ p2) ∨ (p3 ∧ p2))) → (p4 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52111021978119329258675919823 : (((((p2 → (((p3 → p2) ∧ ((p3 ∨ p1) ∧ True)) → (p3 → p5))) ∨ False) → p5) → ((p1 → p2) ∧ ((p3 → p3) ∧ (p2 → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199741894388554288826012217827 : (((p3 ∨ ((p2 ∧ p3) ∧ (p4 ∧ False))) → p4) → ((False ∧ ((p1 ∨ (p4 → (p3 ∨ (p3 ∧ p2)))) ∨ ((p4 → (p2 → p1)) → p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785755513762370074220554378135 : (((p4 ∨ (((p1 → (p3 ∨ p4)) ∨ (p1 ∨ ((p1 ∨ False) ∨ ((p2 ∧ (p3 → (((p3 ∨ p1) ∧ p2) ∨ p3))) ∧ (p5 ∧ p3))))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150673476534640128021668871960 : (((False → (((p4 → (((p3 → p4) → (p5 → (False ∧ p4))) ∧ (p3 → (p2 → p4)))) → p4) ∨ p4)) ∧ True) → (((p4 → p3) ∧ True) ∨ True)) := by
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
theorem thm_5_vars_151956737879084454958708610514 : ((((((((True → (p3 → False)) ∨ False) ∧ p1) → p1) → p3) → p5) ∨ ((False ∧ (p3 → p2)) → (p4 ∧ p1))) → (p5 ∨ ((p4 ∨ True) ∨ p4))) := by
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
theorem thm_5_vars_345465507574781314932119910089 : (p3 → (((((True ∨ (((p5 ∧ False) ∨ (p5 → (False ∧ p4))) ∨ p2)) → p3) → ((True ∨ (p2 ∨ True)) ∧ False)) ∧ ((p1 ∨ p3) ∨ p4)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806724212760534142217262802382 : (((p4 → (((p5 ∧ ((p3 ∧ (p4 → (((True ∨ p2) ∨ p4) ∨ p3))) → p2)) ∧ (True ∧ ((p2 ∧ (True ∨ p4)) ∧ p3))) ∧ (p4 → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_906333475427819713982367160102 : ((((((p4 ∨ False) → (p2 → ((((p2 ∧ False) → True) → (p4 → p5)) ∨ (p5 → (True → p5))))) ∨ p2) → ((p4 ∨ (p2 → False)) ∧ p2)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∨ False) → (p2 → ((((p2 ∧ False) → True) → (p4 → p5)) ∨ (p5 → (True → p5))))) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639229369037353850812939439123 : (((((p4 → ((p2 → p5) → p1)) ∨ (((((True ∧ (p3 ∨ p2)) ∨ p4) ∨ p1) ∨ (((p2 → (p3 → p4)) → p3) ∧ True)) ∧ p2)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49209417681442470286727942336 : ((((True → (p4 ∧ p1)) → ((p1 ∧ (p4 ∧ ((((p5 ∧ False) ∨ True) → (p3 ∧ True)) ∨ (p5 ∧ p1)))) → p5)) ∨ (p1 ∧ (p5 → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205064314153917196736931586088 : (((p3 → ((p5 ∧ False) ∧ p1)) → False) ∨ (p4 ∨ ((True ∧ (p1 ∧ (p5 ∧ (p4 ∧ p5)))) → (((p5 ∧ (False → p5)) → (p1 ∨ True)) ∨ p3)))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303764161966483834561336939058 : (p1 ∨ (((((p4 ∧ p4) ∧ ((p5 → p3) ∨ (p2 ∨ True))) ∨ (p3 ∧ ((True → ((False ∧ (p1 ∧ (False ∧ p2))) ∨ p5)) ∧ p4))) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8842571516217246921552491052 : ((((p1 ∨ (True ∨ ((p2 ∧ ((p2 ∧ (False → p2)) ∨ (False ∨ (True → ((True ∨ p1) ∨ p1))))) → p4))) → (p4 ∨ (True ∨ p1))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638236589387269396480758822475 : (((((True ∨ (p2 ∧ (p4 → ((p5 → p5) ∨ p1)))) → ((p4 ∧ (False → (p3 → (False → ((p3 ∨ p3) ∨ p5))))) ∧ (p5 ∧ p3))) → p3) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p2 ∧ (p4 → ((p5 → p5) ∨ p1)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157467553225586272559098319258 : (((((p5 ∧ (p1 ∧ ((True ∨ (p1 ∧ False)) ∧ (True → (p2 → True))))) ∧ p4) → p2) ∨ (p2 ∧ False)) ∨ ((p3 ∨ ((False → p5) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190875731083317957139712740074 : ((((p2 ∨ (p3 ∨ p4)) → (p5 ∨ True)) → (p2 → False)) ∨ (((((p2 ∨ ((p4 → p2) → p5)) ∨ p1) ∨ False) → (True ∧ p4)) → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171528447154368577834748354760 : ((((((p1 ∨ (((p4 ∧ p1) → p1) ∨ p1)) ∨ (p1 → p3)) → False) ∨ True) ∨ p1) ∨ ((p4 ∧ (p2 ∧ p3)) → (p3 → (p2 ∧ (p2 ∧ p4))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313064172170594221182681957431 : (p3 ∨ (((p5 ∨ ((((False ∨ p1) → False) ∧ ((((p3 → p2) ∧ ((((p3 ∧ False) → p3) → p1) ∨ p1)) ∨ p5) → False)) ∧ True)) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633842570198623858826466550894 : ((((((((p4 ∧ p3) → p5) ∨ (p2 ∧ (((p1 ∨ (p1 ∧ p2)) → (((p4 ∨ p4) ∧ p4) ∨ True)) ∧ p5))) ∧ p1) → (p3 ∨ p1)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40614746900644134183349015440 : ((((((p4 ∨ (p3 ∧ p4)) → ((False ∨ False) ∨ (((p5 ∧ False) ∨ ((False ∧ p4) ∨ p1)) ∧ ((p5 ∧ True) → p3)))) ∨ p1) → False) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315606558172590241534865386198 : (p3 ∨ ((False → p3) ∧ ((((p2 ∨ (p1 → p1)) → p3) ∨ (p5 ∨ (p4 → (p3 → p4)))) ∨ (False ∨ ((p2 → (p2 ∧ (False → p2))) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175856723352051068279454171079 : ((((p1 ∨ (((True ∨ p1) ∧ (p4 ∨ p4)) ∨ p2)) ∨ (False ∧ p1)) ∨ True) ∧ ((p1 ∧ p3) ∨ (False → ((False → (p1 ∨ (p3 → p4))) ∧ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_813574398851556645218917444457 : (((((True → (((((False ∨ (((p4 → False) ∨ p4) → p4)) → p5) ∨ p1) ∧ False) ∧ (((True ∨ (False ∧ p5)) ∨ p1) ∨ p4))) ∧ p5) ∧ p1) → p2) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265816466658896194252298017483 : (True ∧ (p5 ∨ (((p5 ∨ (p4 ∨ ((p3 ∨ (False ∨ (((p3 → p4) ∨ p4) ∧ ((p2 ∧ (p4 → p5)) → p1)))) ∧ p1))) → (p2 ∧ p5)) ∨ True))) := by
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
theorem thm_5_vars_310208090099255174286853356425 : (p2 ∨ ((((p4 ∨ (p4 ∧ ((p2 ∧ p2) ∧ p5))) ∧ p5) ∧ (p4 ∨ p1)) ∨ (((p3 ∧ p2) ∨ ((p1 ∨ False) ∨ p5)) ∨ ((p5 ∧ p3) → True)))) := by
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
theorem thm_5_vars_90920227917039011277134271473 : (((True → False) ∧ ((p3 → (p4 ∨ (((p3 ∨ True) ∨ (False ∨ (False ∨ (p4 ∧ (p1 ∧ ((p4 ∨ p2) ∧ False)))))) ∧ p2))) → (p1 ∨ p2))) → p3) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117878117983088652982941530577 : ((p5 ∧ ((((p3 ∧ (((p2 → False) ∧ p3) ∨ (True ∧ (True ∨ p1)))) ∨ (p4 ∨ (False → p2))) ∨ (p1 ∨ (True → p1))) → p2)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735016397331494832774264105621 : ((((p3 ∨ True) ∧ ((p4 ∧ ((True ∨ ((p1 ∧ p3) → p1)) → p2)) ∨ (((p2 → p1) → (p1 → ((p3 → p1) ∨ False))) ∧ (p1 ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233313353087194083496537615108 : ((True ∨ (p5 ∨ p3)) → ((p5 → ((p3 → p5) ∨ (((p1 → p2) → p4) ∨ p3))) ∧ (((p1 → ((p2 ∧ (True ∧ p4)) → p5)) ∨ p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58935772745507081557592896164 : (((p1 ∧ p4) ∨ ((((((p1 ∧ p5) ∧ p4) → (False ∨ (p5 ∧ p1))) → False) ∨ (p1 ∧ (p3 ∧ (p3 → False)))) ∨ (True ∧ (p1 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147728077609270239512784782154 : ((((((True → p1) ∨ p1) ∧ (p1 → p2)) ∨ ((p5 ∨ p5) → (p5 → (((False ∧ p3) → p2) ∨ p4)))) → p3) ∨ (True ∨ ((p1 ∨ p5) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686656385521538556686399922504 : (((((False ∨ p2) → ((False ∧ ((p5 ∨ True) → p4)) → ((p2 → ((p1 → p5) ∧ p5)) ∨ p1))) → (((False ∧ p5) → p2) → (p3 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594693001805086821307035550003 : ((((((((False → False) ∧ p1) → ((p4 ∨ p3) → p5)) ∧ (p1 → (p2 ∨ (p5 ∧ p3)))) → (p1 ∨ (False ∧ ((p5 → p4) ∨ p5)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157458138021250726352695304148 : ((((True ∨ (p4 ∧ ((p2 ∧ p3) ∨ ((False ∧ (p5 ∨ False)) ∧ (p2 → p3))))) ∧ False) ∨ (p2 ∨ p3)) ∨ (True → (((p1 ∨ p5) ∨ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761657409975247550213094652860 : (((p3 ∧ ((((False → (p3 ∨ p5)) ∧ p5) ∧ ((p1 ∧ p3) ∨ ((p3 → p2) → (p4 → (p4 ∨ (((True ∨ p1) ∧ False) ∧ True)))))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354858695192462299804762919009 : (p5 → (((p1 ∨ p2) → (p2 ∨ (True ∧ ((((p5 → (p5 ∨ ((p2 → False) ∧ ((p2 ∨ p5) ∧ False)))) ∨ p1) ∧ (False ∨ p4)) ∧ p5)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



