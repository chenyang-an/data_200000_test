variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351418368779099143777283907555 : (p4 → ((False ∧ ((((p4 ∧ (p3 ∧ ((p3 → True) ∧ p2))) → True) ∨ ((True ∧ True) ∨ (p1 ∧ False))) → p3)) ∨ (((False → p2) → p5) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233782059591854753330385546047 : ((p3 ∨ (p4 ∨ p5)) → (p3 → (p3 ∧ ((((((p5 ∨ p4) → True) ∧ False) ∨ p5) ∨ False) ∨ ((False ∨ p2) ∨ (((True ∧ p2) ∧ True) ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622128743886320289032827544103 : ((((p2 ∧ ((p1 ∨ (p5 → (((p1 → p1) → p1) → p2))) ∧ ((p4 ∧ p3) ∨ ((p5 ∧ (((p4 ∨ p3) → p5) → p3)) ∨ p5)))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221145441417652158680640555811 : (((True ∨ p4) ∨ p4) ∧ ((((p2 ∨ False) → (p5 → (False ∨ (p4 ∨ p5)))) ∧ (((((True ∧ True) ∨ p3) → p1) → p4) ∧ (False → True))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721311290143642829050691230008 : (((((p3 → p3) → (p4 ∨ p4)) → (((p4 ∨ (((p3 → ((p1 → p1) → (p3 ∧ (True ∧ (p4 ∧ p2))))) ∨ p3) → p3)) ∧ p2) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344311540778975304696736230110 : (p2 → (p3 ∨ (((p4 ∧ True) ∧ ((p4 → True) ∧ (p1 ∨ p5))) ∨ (p1 ∨ (((False ∨ (p4 ∧ p4)) ∧ (((p3 ∧ p4) → False) ∧ p2)) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106055337778204899092446508679 : ((((p5 ∨ (((p2 → (True ∧ p3)) → (p5 → p2)) ∧ p4)) ∨ True) ∧ (((p3 ∨ ((False ∧ p1) ∨ (True ∨ p3))) → p5) → p5)) ∧ (False ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ ((False ∧ p1) ∨ (True ∨ p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205720108940839687865246209234 : (((p3 → p1) ∨ ((p3 ∨ p2) ∨ p5)) ∨ ((((p3 ∧ p5) ∧ (p1 ∨ (((True ∧ p3) ∨ p3) ∨ p2))) ∨ True) ∨ ((p4 ∨ p4) ∧ (True ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711025797750939307509779547935 : (((((p4 ∨ p5) → (p1 → (True → True))) ∧ (((p3 → p5) → ((((p2 ∨ (p3 ∧ p4)) ∨ p3) → p4) → p3)) ∨ (p4 ∨ (False → True)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137012603259306336040384526059 : (((p2 ∨ True) → (((((((p4 → p2) ∨ (p1 ∨ (p4 ∨ p4))) ∧ p1) ∧ (False ∧ False)) ∧ p5) ∨ p2) ∧ (p1 → True))) ∨ (True → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615408028442934320947128539400 : (((((p5 ∧ (((p3 ∨ (((p4 → p2) → p5) → p3)) ∨ (p1 ∨ (p5 → False))) ∨ p5)) ∨ ((p5 ∧ p1) ∨ ((p3 ∨ True) ∨ p3))) ∨ p1) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217209183607835095925325857614 : ((((True → p1) → p1) ∨ True) → (((p1 → (False → p2)) ∧ p1) → (p2 ∨ ((p1 ∧ (((p5 ∨ False) → (p5 → p4)) → p4)) → (True ∨ p1))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118311749962415052386530284730 : ((p1 ∨ (p5 ∨ (((p2 → ((p4 ∧ (((True ∨ False) → (p1 → p5)) ∨ False)) ∨ (p3 ∨ (False → (p4 → p3))))) ∨ p4) ∨ p2))) ∨ (p4 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172998167082929299305488218780 : ((p5 ∧ (((((False ∨ p1) ∧ p5) → p5) → p1) ∧ ((p4 → False) ∧ (p5 → p3)))) ∨ ((p1 ∨ (p3 ∧ (p1 ∧ (False ∨ (p1 ∨ p3))))) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153786041531107409992338876742 : ((p4 → (p1 ∧ (p3 ∨ ((True ∧ (True → (((p5 ∨ p3) → False) ∧ p2))) → ((p5 ∧ (False ∧ p2)) ∧ p2))))) → ((p3 ∨ p2) ∨ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136021415162901102031687129328 : ((((p4 → (p2 → ((p1 ∨ (p5 ∧ p3)) ∨ p3))) → False) → (((p1 ∨ ((p4 → False) ∧ p2)) ∨ (p2 → True)) ∨ True)) ∨ ((p5 ∧ p3) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248304140616472389296013138229 : ((p2 ∨ p2) ∨ (p4 ∨ (((((((p1 ∧ (p1 ∧ p4)) → True) ∨ (p2 ∧ p2)) ∨ p3) ∨ (((p2 ∧ p4) ∨ False) ∨ p1)) → p2) → (p2 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p1 ∧ (p1 ∧ p4)) → True) ∨ (p2 ∧ p2)) ∨ p3) ∨ (((p2 ∧ p4) ∨ False) ∨ p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110680998391192574458753247423 : ((p5 → (p3 ∨ (((False ∧ (p2 → p5)) ∨ False) ∨ (p2 ∨ ((p5 ∨ p3) → (p3 ∨ ((False → (False → False)) ∨ (p1 ∧ True)))))))) ∧ (p3 → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193245975813766495283274299505 : ((((p5 → p3) → p4) ∧ (p3 ∨ (p1 ∧ (True ∨ False)))) → (((((p4 → False) → (p5 → True)) → (p3 → p4)) ∨ (p1 → True)) ∨ (p5 ∧ p4))) := by
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
    cases h8
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
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61628864610254125093135365034 : ((p1 ∧ ((p4 ∧ True) → ((((True ∧ p4) ∨ (p2 ∧ p3)) → (((p4 ∧ p5) ∧ p4) ∧ True)) → (p3 ∧ ((p5 ∨ (p3 ∨ p2)) → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172171208651681784649004930238 : ((((False ∨ (False ∧ False)) ∨ ((p2 ∨ p5) → (True ∧ p5))) ∨ (p5 → (p1 ∨ p5))) ∨ (p2 ∨ ((False ∨ p3) ∧ (((True → p1) ∨ p3) → p5)))) := by
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
theorem thm_5_vars_66641503819460492102447519378 : ((True → ((((p3 ∨ (p3 ∧ (False ∧ False))) ∨ ((p3 → p2) ∨ p3)) ∨ p2) → ((p3 ∨ (((p3 → (True ∧ p5)) → p4) ∨ p4)) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301364529955369535184869991771 : (False ∨ ((((p5 ∨ False) ∧ False) ∨ p5) ∨ ((p5 ∨ (((False ∨ (True → True)) ∨ True) ∧ p3)) → ((True ∧ ((False ∨ p4) → p1)) ∨ (True → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116161531343989125759180327136 : (((p4 ∨ (False → True)) ∧ (((p3 → (False ∧ p4)) ∨ (((((False ∨ (p2 ∨ p1)) ∧ p5) → p2) → p4) → (p2 ∧ False))) ∨ True)) ∨ (p4 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165604897506876077871767029904 : (((((p3 → p4) ∨ p2) → ((p5 ∧ p4) ∧ p5)) → ((((p1 → p2) → p4) ∨ p4) → p3)) ∨ (True ∨ (p5 ∨ ((p4 ∨ (p1 ∨ p3)) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173134679981718432104708381921 : ((p3 ∨ ((((p2 ∨ (False → False)) ∧ (((p1 ∨ p3) → p3) → p4)) ∧ p4) ∧ False)) ∨ (((p5 ∧ ((p3 → p1) ∧ p1)) → p5) ∧ (False → False))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160093681817818526844532503322 : (((p4 ∨ (True ∧ ((p5 → True) ∨ (p1 ∧ (((p3 ∧ p3) ∨ True) ∧ ((p3 ∨ p3) ∧ p1)))))) → False) → (((p2 ∧ True) ∨ (p2 ∨ p2)) → p4)) := by
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
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : (p4 ∨ (True ∧ ((p5 → True) ∨ (p1 ∧ (((p3 ∧ p3) ∨ True) ∧ ((p3 ∨ p3) ∧ p1)))))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h6
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h11 : (p4 ∨ (True ∧ ((p5 → True) ∨ (p1 ∧ (((p3 ∧ p3) ∨ True) ∧ ((p3 ∨ p3) ∧ p1)))))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h13 := h1 h11
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h15 : (p4 ∨ (True ∧ ((p5 → True) ∨ (p1 ∧ (((p3 ∧ p3) ∨ True) ∧ ((p3 ∨ p3) ∧ p1)))))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h16
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h17 := h1 h15
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636368693591322393500781350207 : ((((((p2 ∧ ((True → True) → p4)) ∧ (((p4 → (True → (False ∧ p5))) ∨ p1) ∨ p5)) → ((p2 ∧ ((p5 ∨ p1) → p4)) → p4)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357201689109923403561731871347 : (p5 → ((p5 ∨ p2) ∧ ((False ∨ (p3 → ((p5 → (p2 ∧ p3)) → (p5 → ((((p2 ∨ (p2 ∧ p2)) ∨ False) ∧ False) ∨ (True ∧ p3)))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218632601837778588553373884220 : ((True ∧ ((p4 → p2) ∧ p1)) → ((True ∧ (((p3 ∨ True) → ((p4 → p1) ∧ (p2 ∨ (p2 ∨ p5)))) ∨ (True ∨ p5))) ∨ (p1 → (True ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
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
theorem thm_5_vars_171330418085270590973682431863 : ((((False ∨ (((True → p1) ∨ ((p4 ∨ p4) ∨ p3)) → (p2 ∧ p5))) ∨ p2) ∧ p4) ∨ (p5 ∨ (False ∨ (p5 ∨ ((p5 → p2) → (p3 → True)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63413508297484855608421051337 : ((p5 ∧ (p5 ∨ (((p1 → ((p1 ∧ ((False ∨ p4) ∧ p5)) ∨ p5)) ∧ p2) ∧ ((p1 ∧ (p2 → (p2 → p1))) ∧ (p3 ∧ (True → p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_457081953011950901401604304348 : ((((((True → (False → (((False ∧ True) ∧ True) ∧ ((True ∧ True) ∧ False)))) ∧ (p1 ∧ p2)) ∧ True) ∨ (((p5 ∨ p3) → p1) ∨ (p3 ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_695084951781546557986130621147 : (((((((p5 → (False ∧ p1)) → (p3 ∧ (p4 ∧ (p2 ∨ True)))) ∧ p3) ∨ p2) → ((False ∨ False) ∧ (((p3 ∧ True) ∧ (p3 ∨ True)) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98812574943088561372564524109 : ((True → (((p1 ∧ ((((p3 ∨ p5) ∨ p5) ∨ (False ∨ True)) ∧ p4)) ∨ (((True ∨ (p2 ∨ True)) ∧ False) → (p4 → (p1 ∨ True)))) ∧ p2)) → p2) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76019125256626957248513831433 : ((((((((p3 ∨ (p5 → (p1 ∨ p3))) ∨ p4) → p2) → ((((p2 ∨ False) ∨ p1) → False) ∨ True)) → (False ∨ (False ∧ p3))) → p2) → False) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((p3 ∨ (p5 → (p1 ∨ p3))) ∨ p4) → p2) → ((((p2 ∨ False) ∨ p1) → False) ∨ True)) → (False ∨ (False ∧ p3))) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((((p3 ∨ (p5 → (p1 ∨ p3))) ∨ p4) → p2) → ((((p2 ∨ False) ∨ p1) → False) ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245062566646588133856279939401 : ((p1 ∧ p5) ∨ (((p2 ∧ ((((p5 ∧ p3) ∨ p4) ∨ False) ∨ p1)) ∨ p2) ∨ (((p4 → (p5 ∨ (True → (p4 ∧ False)))) ∨ p4) ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_733045422704986856818820685757 : ((((p2 ∧ p5) ∧ ((p1 ∧ ((p1 ∨ ((p4 ∨ (True ∨ (True ∧ False))) ∨ p5)) ∧ (p5 ∧ p3))) ∨ (False ∨ ((False ∨ (False ∧ False)) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66796303687802987955357578626 : ((True → (p2 ∨ ((p2 → (p3 ∨ (((((True ∨ (p2 ∧ p3)) ∨ ((p3 → p2) ∧ p1)) ∧ (False ∨ (p4 ∧ p4))) → p3) ∨ True))) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709529096175148803455386951298 : ((((True ∨ ((((p3 ∧ p2) ∧ p5) → p4) ∧ True)) → ((p5 ∨ True) → (True ∧ ((True ∨ False) ∧ (((True → False) ∧ (True ∨ p2)) → p3))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- Implications on the right can always be decomposed.
  intro h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h13.left
  let h15 := h13.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h18 =>
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h19 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h20 := h14 h19
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h24 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h25 := h14 h24
        -- False on the left can always be used.
        apply False.elim h25
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h27 =>
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h28 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h29 := h14 h28
        -- False on the left can always be used.
        apply False.elim h29
      case inr h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h30.left
        let h32 := h30.right
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h33 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h34 := h14 h33
        -- False on the left can always be used.
        apply False.elim h34
  case inr h35 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h36 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h37 =>
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h38 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h39 := h14 h38
        -- False on the left can always be used.
        apply False.elim h39
      case inr h40 =>
        -- Conjunctions on the left can always be decomposed.
        let h41 := h40.left
        let h42 := h40.right
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h43 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h44 := h14 h43
        -- False on the left can always be used.
        apply False.elim h44
    case inr h45 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h46 =>
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h47 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h48 := h14 h47
        -- False on the left can always be used.
        apply False.elim h48
      case inr h49 =>
        -- Conjunctions on the left can always be decomposed.
        let h50 := h49.left
        let h51 := h49.right
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h52 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h53 := h14 h52
        -- False on the left can always be used.
        apply False.elim h53
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41664917077884403211742152319 : ((((((False ∨ (True → p2)) ∧ p4) ∧ p3) ∨ (p1 ∧ (((False → ((False → False) ∧ p3)) ∧ p5) ∧ (p2 ∧ ((p1 ∨ p1) → False))))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55498932066108577801720639877 : ((((p3 → (p4 → True)) → (p2 ∧ p5)) → ((p1 → p3) → (p3 ∧ (((p1 ∨ p3) → (((False → (p3 ∨ True)) ∨ p1) ∧ True)) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25520859722677335490930110326 : (((p2 ∨ (p5 ∧ False)) → (((p3 ∧ ((False ∨ (p3 ∨ p4)) ∧ ((True → ((False ∧ True) ∧ (p5 ∨ (p4 → p1)))) ∨ p4))) ∧ p1) ∨ True)) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115732048313237615112739085716 : (((((p3 ∨ p4) ∨ True) ∨ (p3 → p1)) → (p2 ∨ (((((p5 → p4) ∧ (p3 ∧ True)) ∨ p1) ∨ ((p4 ∧ False) → False)) ∧ p4))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254669636786743547942818547579 : ((p3 ∧ p2) → ((p3 ∧ p5) → ((((((p1 ∧ p2) ∨ True) ∨ (p5 → p1)) ∧ ((p3 ∨ p4) ∧ p1)) → ((p2 → p4) → (p5 → False))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607324923921197774040648325384 : (((((((p3 ∨ p4) ∧ p1) → ((((p1 → p1) ∨ (True ∧ ((False ∧ (p3 → p5)) ∧ p4))) ∧ (p5 → (p3 → p2))) → p3)) ∧ p3) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_217125338075224712807450893178 : ((((p4 ∨ p2) ∨ p2) ∨ p4) → (((((((False → (p4 ∧ ((p5 ∧ False) ∧ p5))) ∨ p2) ∨ p3) ∧ p4) ∧ p2) ∧ False) ∨ ((p2 ∧ False) → p5))) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116658398854351390590743464639 : (((p4 → True) ∧ ((((((p5 ∨ False) → p1) → p2) ∧ ((p2 ∧ (((p2 ∧ (p1 ∧ p2)) ∨ True) ∧ p2)) ∨ p3)) ∨ p3) ∧ p1)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694732448251815038339925974827 : ((((p3 ∨ ((False ∧ p1) ∨ (p3 ∧ ((p1 ∧ (True ∨ p3)) → (p1 → p3))))) ∨ ((p2 ∨ (True ∨ (((p2 ∨ p1) ∨ p3) ∧ p5))) ∨ False)) ∨ False) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110713859218060406076392567965 : ((((((((p3 → p2) ∨ ((p1 → p4) → p1)) ∨ (True → p3)) → ((((p5 → p5) → p4) → False) → p4)) → p5) ∧ p4) ∧ False) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68201948273146944246895849231 : ((p3 → ((p3 ∧ (((p4 → ((p5 ∨ True) → ((p4 → p5) ∨ (True ∧ True)))) → (True → False)) ∧ (p5 → (p1 ∧ (True ∧ p2))))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743552551427536574752350029680 : ((((True ∧ True) → (((((p4 ∧ ((p1 ∨ (False ∨ (p4 ∧ False))) ∧ p3)) ∨ (p5 → (False → p2))) → False) ∧ p4) → ((p3 ∨ p4) → p1))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : ((p4 ∧ ((p1 ∨ (False ∨ (p4 ∧ False))) ∧ p3)) ∨ (p5 → (False → p2))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h12 := h5 h9
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h2.left
    let h15 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h1.left
    let h17 := h1.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h18 : ((p4 ∧ ((p1 ∨ (False ∨ (p4 ∧ False))) ∧ p3)) ∨ (p5 → (False → p2))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- Implications on the right can always be decomposed.
      intro h20
      -- False on the left can always be used.
      apply False.elim h20
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h21 := h14 h18
    -- False on the left can always be used.
    apply False.elim h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196699979919635929031115737644 : ((((False ∨ (p4 ∨ (p5 ∨ p2))) ∨ p5) ∧ p5) ∨ ((p5 → ((((p1 → (p1 → True)) → p2) ∨ (p3 ∧ False)) ∨ p1)) → (True → (p1 ∨ True)))) := by
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
theorem thm_5_vars_248261140769263143515287447066 : ((p2 ∨ p2) ∨ ((True → ((p4 ∨ False) ∨ ((p2 ∧ p4) → ((False ∧ (((p1 → p5) ∨ (p2 ∨ p3)) ∨ ((p4 ∧ p5) → p5))) ∨ p2)))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148869541363455267514488083679 : (((((p5 ∧ p3) ∧ True) ∧ p4) ∨ (p3 ∨ ((((p3 ∨ (p2 ∨ p2)) ∧ p3) ∨ False) → (p2 ∨ (False → p1))))) ∨ ((p4 ∨ p4) ∧ (False ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161777274400148828957636697744 : ((p4 ∨ (p1 ∧ (((((False → p3) ∧ p3) → p5) ∨ (p5 ∨ p2)) → (((True ∧ False) ∨ p5) ∧ p2)))) → ((p5 ∧ p1) ∨ ((False ∨ p2) → True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159163678244808619423524549291 : ((p1 → ((((True ∧ (True ∨ ((p4 ∧ (p2 ∨ p5)) → (p4 → p4)))) → p5) ∧ False) ∨ (False → False))) ∨ ((False ∨ (False → p4)) ∨ (p1 → False))) := by
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
theorem thm_5_vars_213219488000617338073959242490 : ((((p5 → p1) ∨ p1) ∧ p1) ∨ ((((((p1 → p1) ∨ p4) → (False ∨ True)) → (p3 ∨ (p3 ∧ p1))) ∨ p4) ∨ (True ∨ ((p5 ∧ p2) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255181895925919435380630105822 : ((p4 ∧ p4) → ((((p5 ∧ (p3 → ((p2 ∨ p1) ∧ p2))) ∨ ((p1 ∧ p5) ∧ p1)) → (True → (p3 ∨ ((p1 → p3) → (False ∧ p1))))) ∨ p4)) := by
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
theorem thm_5_vars_248704187202939063305625931852 : ((p3 ∨ p2) ∨ (((True → ((True ∨ (p1 → p4)) ∨ (p5 ∧ ((p3 ∨ p4) → p4)))) ∨ p5) → (p2 → (((p5 → p1) ∨ (p2 → p2)) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135006349884100045713485675720 : (((False ∨ (((((p3 ∧ (False → (p2 → (p3 → p5)))) ∨ ((p1 → p2) ∧ p4)) ∨ p1) ∨ True) ∧ p1)) ∧ (p4 ∨ p1)) ∨ (p4 ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353552408814629846153965124599 : (p4 → (p3 ∨ ((p3 ∨ ((False ∧ p3) ∧ ((p3 → (((False ∧ p2) ∧ p1) ∧ (p5 ∧ p4))) → p3))) ∨ (True ∧ (p3 → ((p1 → True) ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214758692634168143997864804590 : (((p5 ∧ p2) ∨ (True ∧ p5)) ∨ (((False ∨ (p1 → p4)) ∧ p4) → ((p2 ∨ p4) ∧ (p3 ∨ (((True ∧ ((p5 ∧ p5) ∨ p3)) ∧ False) → p1))))) := by
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
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- False on the left can always be used.
      apply False.elim h12
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62207701095987886511551564001 : ((p3 ∧ (((p5 → p3) ∨ (((p2 ∨ (False → ((p4 ∧ True) ∧ (((False ∧ p1) → False) → (p4 ∨ (p4 → p1)))))) ∧ False) ∧ p5)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645202915664581610597040755514 : ((((p3 ∨ ((p1 → p5) ∧ (p4 → (p4 ∧ (p4 → (False ∨ (p5 ∧ (p4 ∨ ((True → (p1 ∧ (p5 ∧ (p3 ∨ p3)))) → p5))))))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709651158601121120600761622763 : ((((p3 ∨ (p5 ∨ (((p4 → False) → p5) ∨ p5))) → ((p2 ∨ p5) → ((p5 ∧ ((True ∧ p3) ∧ p2)) → ((p4 ∨ (p2 → p2)) ∧ p2)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- One of the premise coincides with the conclusion.
          exact h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h26
        -- One of the premise coincides with the conclusion.
        exact h26
      case inr h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h29
          -- One of the premise coincides with the conclusion.
          exact h29
        case inr h30 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h31
          -- One of the premise coincides with the conclusion.
          exact h31
  -- Conjunctions on the left can always be decomposed.
  let h32 := h3.left
  let h33 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h34 := h33.left
  let h35 := h33.right
  -- Conjunctions on the left can always be decomposed.
  let h36 := h34.left
  let h37 := h34.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h38 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h39 =>
      -- One of the premise coincides with the conclusion.
      exact h38
    case inr h40 =>
      -- Disjunctions on the left can always be decomposed.
      cases h40
      case inl h41 =>
        -- One of the premise coincides with the conclusion.
        exact h38
      case inr h42 =>
        -- Disjunctions on the left can always be decomposed.
        cases h42
        case inl h43 =>
          -- One of the premise coincides with the conclusion.
          exact h38
        case inr h44 =>
          -- One of the premise coincides with the conclusion.
          exact h38
  case inr h45 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h46 =>
      -- One of the premise coincides with the conclusion.
      exact h35
    case inr h47 =>
      -- Disjunctions on the left can always be decomposed.
      cases h47
      case inl h48 =>
        -- One of the premise coincides with the conclusion.
        exact h35
      case inr h49 =>
        -- Disjunctions on the left can always be decomposed.
        cases h49
        case inl h50 =>
          -- One of the premise coincides with the conclusion.
          exact h35
        case inr h51 =>
          -- One of the premise coincides with the conclusion.
          exact h35
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45337322110890941254314563218 : (((p3 ∧ (p1 ∨ (((False → (((p3 ∨ p2) ∧ p4) ∨ (p3 ∧ False))) → ((p4 ∧ p1) → True)) ∨ (((p4 ∨ p2) ∧ p3) ∧ p5)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87389685601030622271317337042 : (((p2 ∧ (((p5 ∨ p2) ∨ p3) → False)) ∧ ((p2 ∨ False) ∧ ((False → (((p4 ∨ p1) ∧ (p5 ∧ p3)) ∨ (p2 → p3))) ∨ (p3 ∧ p5)))) → False) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h10 : ((p5 ∨ p2) ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h11 := h5 h10
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h15 : ((p5 ∨ p2) ∨ p3) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h16 := h5 h15
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53720221400940354635120490192 : (((p5 ∨ ((p4 ∧ p2) ∨ (((p4 ∧ p4) ∧ True) ∨ p1))) ∧ ((((p3 ∧ p4) → p1) → (p5 → (p2 ∧ (True ∧ p3)))) → (True → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118646430583195863330619267635 : ((p4 ∨ (True ∧ ((p3 ∨ p3) ∨ ((True → (((False ∨ p5) → (False ∨ ((p1 → (p3 → p4)) → (p1 → p2)))) ∨ p2)) ∨ True)))) ∨ (p2 ∨ p3)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200506065861250179719480769012 : (((p5 ∧ p4) → ((p2 → (True → False)) ∨ p2)) → (p4 → (p4 ∧ ((((p4 ∧ False) → ((p5 ∧ (p3 → p5)) → True)) → (p5 ∨ p3)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594851872040195369699306034450 : ((((((p5 ∨ ((p5 ∨ p2) → (p3 → ((False ∨ p3) ∧ p4)))) → (p4 → p3)) ∧ ((((p3 ∨ (p2 → True)) → p3) ∨ p1) ∨ p2)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773619431003292452548445363300 : (((False ∨ ((p3 ∧ ((p2 ∧ (p5 → (False → ((p2 → ((False ∨ p3) → p3)) ∧ ((False ∧ p4) ∨ False))))) ∧ ((p5 ∧ True) ∨ p5))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40189634389276691691788673243 : (((((p2 → (p1 → p4)) ∧ ((p5 ∨ ((p5 ∨ (p1 ∧ ((p5 ∧ (p2 → p5)) → (p1 → p1)))) ∧ True)) ∨ (p1 ∨ p5))) ∧ p4) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179067005277640637001914664791 : ((True ∧ ((p5 → (True ∧ ((((p5 ∨ p4) → p2) ∨ p2) ∧ p3))) → p2)) ∨ ((p1 ∧ ((p2 ∧ p5) ∨ (p4 → ((True ∨ p1) ∧ p3)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165412399715807894356025860333 : (((((((p5 ∧ (p5 ∨ True)) ∧ False) ∧ False) ∧ (True → p2)) → p3) → (p3 ∧ (p5 ∨ p4))) ∨ (p3 ∨ ((p5 ∨ p2) → ((False ∧ p2) → p1)))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314858923466065802255848226303 : (p3 ∨ ((((p4 ∧ (p4 ∨ True)) ∨ (p1 → (p5 → (p3 → p4)))) → p1) → (p1 → ((p2 ∨ (False ∧ (p5 → p1))) → ((p2 → p4) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354919103870959902876566074534 : (p5 → ((p1 ∨ ((p4 ∧ p3) ∨ (p3 ∨ ((p2 ∨ p4) ∨ (p2 → (p3 ∨ (((p1 → False) → ((p2 ∨ p3) ∨ p1)) ∧ (p2 → p5)))))))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700479935678417756314049900807 : ((((p2 ∨ (((p2 ∧ p5) → p5) ∨ (True ∨ ((p2 ∨ p1) ∨ True)))) → ((p2 → (((p3 ∧ True) ∧ p3) ∧ (p1 ∨ p5))) ∧ (True ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750442463495384605787934861993 : (((True ∧ (((p5 ∨ (p4 ∧ (True → ((p5 → p1) ∨ ((False ∧ (p3 ∧ p3)) ∨ p1))))) ∨ (p1 → (p3 ∨ p3))) ∨ ((True ∧ p1) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246284713057743480095426923810 : ((p4 ∧ p4) ∨ (((p3 ∧ True) ∨ p3) → ((p1 ∧ ((p1 ∧ True) → p4)) → ((p5 ∨ (p5 ∧ (((p2 ∨ (p4 → False)) ∨ p2) → p4))) ∨ p1)))) := by
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
  cases h1
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140393872946588663808334076393 : (((True → (p2 ∨ (p1 ∨ ((((p2 ∨ ((p4 ∨ p1) ∨ (p2 ∨ p3))) ∨ p3) → p3) ∧ p2)))) ∨ (p1 ∧ (p4 ∧ p2))) → ((p4 → p2) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262397934810104613717759914422 : (True ∧ (((p1 ∨ p5) → ((((True ∧ (p2 ∨ (p1 → p2))) ∨ (p4 → (False ∨ (True ∨ p2)))) → ((p4 ∧ p5) ∨ False)) ∨ (p2 ∧ p5))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608914319455744324314655186075 : (((((((p3 ∧ (False ∨ p3)) ∨ (p2 ∧ ((False → p4) ∧ (p2 ∧ (True → p1))))) ∨ ((((p4 ∨ p2) → True) → p4) → False)) ∨ p3) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_226211660976310421264078675475 : (((p2 ∨ p2) ∨ p3) ∨ (p3 ∨ (p3 ∨ (p2 ∨ (((((p3 → False) ∧ True) ∨ True) → ((False ∧ (((p1 ∨ p2) ∨ False) ∨ p2)) → p1)) ∨ p4))))) := by
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
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40613141904623635430797940560 : (((((((p3 ∧ (p3 → p3)) → p5) ∨ (((p1 → p5) ∨ True) ∨ (p2 ∧ ((p3 ∨ ((p3 ∨ p4) → p3)) ∨ p5)))) ∨ p5) → p1) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_972076175807053517377768376737 : ((((True ∨ p1) → ((((p5 ∨ p4) → True) ∧ (((((True ∨ p4) ∨ p2) → (p4 → p2)) ∧ p4) ∧ ((p3 → p1) ∨ (p5 ∨ True)))) ∧ p3)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588298463716078563381393073873 : ((((((p2 → (p3 ∨ ((p4 ∨ p3) ∧ p4))) → (((False ∨ (p5 → (((p3 → False) → True) → (False ∧ p2)))) ∨ p3) → p3)) ∨ True) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251615629701240482451168805169 : ((p3 → p1) ∨ (((((p1 ∨ p4) ∨ p2) ∨ ((p2 ∧ (False ∧ ((p1 → p5) → p4))) → False)) → (p1 → p1)) ∨ (p2 ∧ (True ∨ (p4 ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h6 =>
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304689785299332493213455250515 : (p1 ∨ (((((p3 ∧ p3) ∧ (p1 ∧ p3)) ∨ (True → ((p4 ∨ (((p5 → False) ∧ (p1 ∨ (p5 ∨ p1))) ∨ True)) ∧ p3))) ∨ p2) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137409101226609761265792395782 : ((p3 ∧ (p3 → (((True → ((p3 ∧ p2) ∧ ((p5 → (p1 ∧ (p4 ∨ True))) → (False ∧ p2)))) → p5) ∧ (False ∨ True)))) ∨ (p2 ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57807986846571189489693435666 : (((p2 ∧ (p3 ∨ p4)) → (((p5 ∧ p2) → (False ∧ ((p1 ∨ (p3 ∧ p3)) ∧ (True ∨ ((p2 → p2) → p4))))) ∨ (False → (p5 → p3)))) ∨ p4) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228096072713603666543098273937 : ((p4 ∧ (p1 ∨ p4)) ∨ ((p3 ∨ p5) → ((p1 ∧ (((False ∨ p5) ∨ True) ∧ ((((True ∧ p1) ∨ (p4 → p2)) ∨ p1) → (False ∧ p2)))) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208282619396774931522345472023 : (((p1 ∨ p3) ∧ (p2 ∨ (p3 ∧ p4))) → ((((p4 ∨ True) ∧ p2) ∨ ((p1 → p2) ∧ (((p3 ∨ (False ∧ (p5 ∧ True))) → p4) ∨ p3))) ∨ p4)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219248812304236630870846300850 : ((p1 ∨ ((p2 → p3) → False)) → (((p5 ∧ False) ∧ p3) ∨ ((p2 ∨ (p5 ∨ ((True ∨ (((p5 → (p1 → p5)) ∨ p1) ∧ p4)) → p1))) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322647612850805293761206388008 : (p5 ∨ ((((p3 → p4) ∧ ((p1 → ((p3 ∨ (p2 → (p4 ∨ False))) ∧ (p1 → p2))) → ((((p1 → p3) ∧ True) → p4) → p5))) ∧ p3) → p4)) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253621981833942473168444249222 : ((p1 ∧ True) → ((((((p5 → p2) ∧ p2) ∨ p5) ∨ ((p2 ∨ p2) → False)) ∧ (True ∨ (p5 ∧ True))) → ((p3 ∨ (p3 → (p3 ∧ p2))) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h1.left
        let h11 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h1.left
        let h16 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h1.left
        let h20 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Conjunctions on the left can always be decomposed.
        let h24 := h1.left
        let h25 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h26 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h1.left
      let h29 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Conjunctions on the left can always be decomposed.
      let h33 := h1.left
      let h34 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166314530495921436896377508909 : ((p5 ∧ ((False → ((p1 → p2) ∨ (((False ∨ (p1 ∨ p5)) ∨ True) ∧ (p1 → True)))) ∨ True)) ∨ (((p3 ∨ False) ∧ ((p4 ∨ p3) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624129068688204852877399070979 : ((((p2 ∨ (p3 ∧ (((((((p4 ∨ p2) ∨ p5) ∧ (False ∨ (p5 ∨ p3))) ∨ p3) → p2) ∧ (p3 ∧ p2)) ∧ (p1 ∧ (True → True))))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708889283420142407957248117768 : ((((((p1 ∧ (p1 → p3)) ∧ True) ∨ (True ∧ True)) → (p3 ∧ (((((p4 ∧ (p4 ∧ p2)) → (p2 ∨ False)) → p4) ∨ (p4 ∧ p4)) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



