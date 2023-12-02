variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337345376132255242182740734331 : (p1 → (((((True ∧ (True → p3)) → ((p2 ∨ p3) ∨ p2)) ∧ (((p5 ∧ p2) ∨ (p3 ∨ (p2 ∧ p1))) ∧ False)) ∨ True) ∨ ((False ∧ p1) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303722647941583459562489740952 : (p1 ∨ ((((True ∧ ((False ∧ ((False → (True ∧ (False → p2))) ∨ True)) → p2)) ∧ ((p5 ∧ (p5 ∧ p1)) ∨ ((p2 → p2) ∧ p5))) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44529518619947923332834377489 : (((((p5 → (((True ∨ False) ∨ p1) ∧ (p5 ∨ p4))) ∧ p5) → (p4 ∨ ((p4 ∧ (p1 ∨ (((p4 → p2) ∨ True) → p4))) ∨ p4))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161966642101370866590483221868 : ((p2 → (True ∨ ((p5 → (((p3 ∨ ((p3 ∨ True) ∧ p2)) ∧ p5) → ((p2 → p1) → False))) → p2))) → (p4 ∨ (p3 ∨ (p1 ∨ (False → p4))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157738979133743245487033311513 : ((((((p4 ∨ p1) ∨ p5) ∧ (p1 ∨ (p3 ∨ (p1 → True)))) ∧ p5) ∧ (p2 ∨ ((False ∨ False) → p1))) ∨ (p4 → ((p4 → (p3 ∧ p4)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209522258028490583118617207402 : ((p4 → ((True ∨ p1) ∧ (p5 ∧ p1))) → (p2 ∨ (((False ∧ False) ∧ p2) ∨ (((p4 → p5) ∧ p1) → (((p5 → p2) ∧ p3) → (False ∨ p1)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345670917954189013741919478030 : (p3 → ((p1 ∨ ((p2 ∨ ((((p2 ∨ (p5 → (p1 → ((True ∨ p5) → (p2 ∧ (p2 → p3)))))) → False) ∧ p1) ∨ p5)) ∧ (True ∨ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50293536607409231916509080790 : ((((False ∨ (((((p4 ∧ (p2 ∧ (p4 → True))) → p1) ∨ p1) ∧ p1) → False)) ∧ (p4 ∨ (False ∧ p4))) ∨ (((p2 → p3) ∨ True) ∨ p1)) ∨ p4) := by
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
theorem thm_5_vars_118159342599280959318185767296 : ((False ∨ ((p1 ∧ (False → p2)) ∧ (((p4 → (((p1 → (p4 → (p2 ∧ p3))) → False) ∧ (True ∧ False))) ∧ (p4 ∨ p1)) ∨ p3))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158955430206682480426783249631 : ((p2 ∨ (p1 ∧ ((True ∧ p3) ∨ (((((p3 ∧ (p2 ∨ p2)) ∧ (p3 → p3)) ∨ p2) ∨ True) → True)))) ∨ (((True ∨ True) → False) → (p4 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55156898711242457352671831293 : (((((p5 → p3) → (p2 ∨ p1)) ∨ p1) ∨ ((True ∨ (p5 → ((p4 ∨ p3) ∧ False))) ∨ ((p3 ∧ p4) ∧ ((True → p2) → (False → p4))))) ∨ False) := by
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
theorem thm_5_vars_135603136613099778645671483653 : ((((p2 ∧ p2) ∧ ((p4 → (p2 → (p5 ∧ (((True → p2) ∧ False) → p5)))) ∧ False)) ∨ ((p1 → (p2 ∨ p2)) → p4)) ∨ (p3 → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192440170483198604955583457386 : (((((p4 ∨ p2) ∨ (p3 → (True → p2))) → p3) ∨ p3) → ((p4 → (((p5 → p5) → (False ∧ p3)) ∨ True)) ∨ (p2 → (p1 ∧ (p1 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60068118586906605261042477808 : (((p2 ∨ p2) → (p1 ∧ (((p5 ∧ p3) ∧ (p3 ∧ True)) ∧ (((((p1 ∨ False) ∧ p3) ∨ (p1 → (p5 ∨ p4))) ∧ p1) ∨ (False → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53010943838415451399279370753 : ((((False → ((p1 → (p3 ∨ False)) ∧ False)) ∨ (False ∧ (True ∨ p5))) ∧ (((((p1 ∧ p3) ∧ (True → p5)) ∨ p4) ∨ p3) ∨ (True ∨ p4))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52120076620304762206072579532 : (((((True ∨ (p1 ∧ p2)) → (((p5 ∧ (True → False)) ∧ p5) ∨ (p1 ∨ True))) → p4) → (((((p4 ∨ p2) ∨ p5) → True) → p1) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619714798762432492539875481887 : (((((p5 ∧ p4) ∧ (p5 ∧ ((True ∧ (p5 ∨ ((p4 ∨ (p2 ∧ (p3 ∧ p5))) ∨ p1))) ∧ (((False ∨ (p4 ∨ p2)) ∧ True) ∧ p4)))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238114911112746393650333815847 : ((True ∨ p3) ∧ ((((p5 ∧ ((False → (p3 → p3)) ∨ (p3 ∧ (p1 → True)))) ∧ (((p3 ∨ p4) ∧ p4) ∧ ((False ∨ True) ∧ p3))) ∨ p3) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212983876002834268375309373858 : ((p4 → (p1 ∨ (p1 → p4))) ∧ ((False ∧ (p1 ∨ p1)) ∨ ((True ∧ p4) → (((p5 → ((p2 ∧ (p4 → (False ∧ p3))) ∧ True)) ∧ p5) → p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
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
  let h7 := h3.left
  let h8 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h9 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h10 := h5 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h13 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h14 := h12 h13
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257912809267047660596036998176 : ((p4 ∨ False) → ((((((p5 ∨ True) ∧ ((p1 → p5) ∨ p1)) → p3) → ((p3 ∨ ((p3 ∨ p3) → ((p3 ∨ p2) ∧ p1))) ∨ True)) ∨ p4) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117546629013993658811159612118 : ((p2 ∧ ((((p2 ∧ (((p5 → True) ∧ ((p2 ∧ (p3 ∨ False)) → p3)) → False)) ∨ p5) ∧ p4) ∨ (((p1 ∨ False) ∨ p4) ∧ p2))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181088017730179868638457980755 : (((False → True) → ((False ∧ (p5 ∨ True)) → ((True → (True ∨ p1)) ∧ p3))) → (((False → (p3 → p4)) → p2) → ((p1 ∧ (p1 ∨ p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40949526854508603214385653055 : ((((((((False ∧ ((False ∧ False) ∧ ((True ∧ p1) → ((p2 ∧ p4) ∧ p3)))) ∨ p1) ∨ p5) ∨ p3) ∨ (p4 ∨ p5)) ∨ (True ∨ p1)) ∨ p4) ∨ p1) := by
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
theorem thm_5_vars_763724716321817080987247388521 : (((p3 ∧ (False ∨ (p3 ∨ (((p2 → (p1 ∧ p1)) ∨ ((p1 → (((False ∧ p1) → ((True → p5) ∧ True)) ∨ False)) → (p4 ∨ p3))) → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245616298352411313939690360820 : ((p3 ∧ False) ∨ ((p3 ∨ (True ∧ p5)) ∨ ((p5 ∨ (False → (p4 → (False ∨ p5)))) ∨ ((p3 ∨ ((p5 ∨ (False ∧ p1)) → (p1 ∨ p5))) ∨ p5)))) := by
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
theorem thm_5_vars_185890603992152956029738978763 : (((((p3 ∨ (p2 ∨ (p5 → p3))) ∧ False) ∨ (True → p1)) ∧ p4) → (((p3 ∧ p3) ∧ (p1 ∧ (False ∧ (p1 → ((p2 ∧ p5) → p3))))) ∨ p4)) := by
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
      -- False on the left can always be used.
      apply False.elim h6
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h6
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325177624855737078962881060407 : (p5 ∨ (True ∧ (p3 → (((((p4 → False) ∧ p4) ∨ p1) → (p1 ∧ ((True ∧ (True → True)) → (p1 ∧ False)))) ∨ ((p1 ∨ (False ∨ p3)) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_198002826729202008286997550690 : (((False → p1) ∧ (False ∧ ((True → p2) ∧ p5))) ∨ ((p3 → (((p3 ∧ ((p4 ∨ p3) ∨ p4)) ∨ p1) → (((p1 → True) → p2) ∨ p3))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h8 =>
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651011602079929582757036948008 : ((((((p2 → p5) ∨ (p2 → (p1 → p2))) → (p3 ∨ (p5 → (p4 → ((False ∧ (((False → p2) → p5) ∧ p3)) ∨ p5))))) ∧ (False ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184345786461674010090236497034 : (((p3 ∧ ((p3 ∨ p4) ∨ ((p2 → (p3 ∨ p4)) → p1))) → False) ∨ ((p1 ∧ p2) → ((p3 → ((True ∧ p2) → p2)) ∧ ((p5 ∨ p2) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111925843940072302058938189632 : ((((p3 → (p5 ∨ (((True ∧ p3) → True) ∨ (p3 → (False → p3))))) → (False ∧ (p2 → (((p5 ∨ p5) ∨ p1) → p4)))) ∨ False) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217972691253855750780248333313 : (((p3 ∧ True) ∧ (True ∨ p3)) → (((p2 ∨ ((((False → p5) ∧ p4) ∧ False) ∨ (p5 → (True ∨ (p4 ∧ p3))))) ∨ (p2 ∨ (p3 ∧ False))) ∨ p2)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175134480843107544333851728704 : ((p5 ∧ (((True → (False ∨ p2)) ∨ ((False ∨ False) ∨ ((True ∨ p1) → p5))) → p5)) → (p2 → ((p1 ∧ (((True → p3) ∧ True) ∧ p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54277457420339874639274003648 : ((((True ∧ (p1 ∧ p3)) ∨ ((True → False) → p3)) ∧ (((True ∨ p3) ∨ p5) ∧ (p1 ∨ (((True ∨ p5) ∧ (p3 ∨ False)) ∧ (False → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209382811137284231716981320440 : ((p1 → ((p4 ∨ False) ∧ (False ∧ p2))) → ((p1 ∧ ((p4 ∧ (p3 → (p5 ∧ False))) → p3)) → ((False ∧ (p2 ∧ (p4 ∧ (p1 → p5)))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205998898329294275215012857408 : ((p1 ∧ (p3 ∨ ((p3 ∧ False) ∧ False))) ∨ (p3 ∨ ((True ∨ (p1 ∧ (((False → (p5 ∨ p1)) → p5) ∨ (p4 ∧ p1)))) ∨ ((p2 → p4) ∨ False)))) := by
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
theorem thm_5_vars_593916390980223244107662779410 : (((((((p3 ∨ p2) ∧ (p2 ∧ (False → (p1 ∨ ((p4 ∨ p5) ∧ False))))) → ((True → p4) ∨ p1)) ∨ ((p2 ∨ p2) → (False → p3))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_927674026492797855590032449722 : (((((p3 ∨ (False ∨ ((False ∧ (p2 ∧ True)) ∨ p4))) → p5) ∧ (((p3 ∧ (False ∧ p3)) ∨ p4) ∧ (((p4 → p1) ∧ p4) ∧ (False ∨ p1)))) → p5) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h5.left
    let h13 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h16 =>
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h18 : (p3 ∨ (False ∨ ((False ∧ (p2 ∧ True)) ∨ p4))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h19 := h2 h18
      -- One of the premise coincides with the conclusion.
      exact h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38779354759429766097212351468 : ((((((p1 → True) ∧ p4) → p3) ∨ (p5 ∧ ((p3 ∧ (p5 ∨ False)) ∧ (p1 ∧ ((((p2 ∨ p4) → p4) → p2) ∧ (True ∨ p5)))))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37261882527984666510927785439 : ((((p3 ∧ (p3 ∧ (p5 → (((((p5 ∧ (((p4 ∨ p4) → True) ∧ ((p3 → p3) ∧ False))) → p3) → p3) ∧ p3) ∧ False)))) ∧ True) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171473976520800005525007878864 : (((p3 ∨ (((p4 ∧ False) ∨ p1) ∨ (False ∧ (p4 ∨ (p3 ∨ (p2 → True)))))) ∧ p2) ∨ (False → (((p4 ∧ (True → p2)) → p3) → (p1 → p2)))) := by
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
theorem thm_5_vars_133943439634357434044274576741 : (((p1 → ((True → (((p5 → (p2 → p4)) → (True → False)) → (((p1 ∨ (False → p5)) → p5) → p3))) → p2)) ∧ False) ∨ (p4 ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137948098555011228276721021262 : ((p5 ∨ (((((p3 → (p5 → p2)) → (((False ∧ False) ∧ (p4 ∨ p2)) ∨ ((True ∨ p2) ∨ p2))) → p4) → p2) ∨ p4)) ∨ ((p4 → p4) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55868786670104642428706538551 : (((p5 ∧ (p3 ∨ (p1 ∨ False))) ∧ (((False ∨ p3) ∨ ((False ∨ p4) → p1)) ∧ ((p2 ∧ p5) ∨ ((False ∨ p4) ∧ (False → (False ∨ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234128566332414714639531409189 : ((True → (p3 ∨ p3)) → (((p3 → (True ∨ p4)) → ((p2 ∧ ((p5 ∧ False) → ((True → (p4 ∧ (p1 ∧ p5))) ∨ False))) ∧ p4)) ∨ (False → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199849360593417391938973548669 : (((p3 ∧ (p2 → (p2 ∧ False))) ∧ (p2 ∧ True)) → ((((p3 ∨ p5) ∧ (p2 ∨ (((p4 ∨ (p4 ∧ p5)) → (p2 → p4)) ∨ p4))) → p2) → p4)) := by
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
  let h7 := h4.left
  let h8 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h9 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h10 := h6 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228192156235763915055458966801 : ((p5 ∧ (p4 ∧ p5)) ∨ (((p1 → (((True ∨ p5) ∧ p2) ∧ (p5 ∧ (False ∧ p5)))) → (p2 ∨ (((p3 ∧ p1) ∧ p1) → p5))) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157048999955523926091287906240 : (((p1 ∧ (p3 ∧ ((p1 → p3) ∨ ((False ∨ (True → (((p3 ∨ False) ∧ p4) ∨ True))) → p3)))) ∨ True) ∨ (((p2 → (False ∨ p2)) ∨ False) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81172222828868208025539750929 : (((p3 ∧ (((False ∨ (p2 ∧ (True → True))) ∧ (((p5 ∨ p1) ∨ True) ∧ ((p5 → p4) ∨ (p4 ∨ p5)))) ∨ False)) ∧ ((True ∧ True) → p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h8.left
      let h14 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h17 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h18 : (True ∧ True) := by
              -- Conjunctions on the right can always be decomposed.
              apply And.intro
              -- True on the right can always be proven directly.
              apply True.intro
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h19 := h3 h18
            -- One of the premise coincides with the conclusion.
            exact h19
          case inr h20 =>
            -- Disjunctions on the left can always be decomposed.
            cases h20
            case inl h21 =>
              -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
              have h22 : (True ∧ True) := by
                -- Conjunctions on the right can always be decomposed.
                apply And.intro
                -- True on the right can always be proven directly.
                apply True.intro
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h3, we can now drive its conclusion.
              let h23 := h3 h22
              -- One of the premise coincides with the conclusion.
              exact h23
            case inr h24 =>
              -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
              have h25 : (True ∧ True) := by
                -- Conjunctions on the right can always be decomposed.
                apply And.intro
                -- True on the right can always be proven directly.
                apply True.intro
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h3, we can now drive its conclusion.
              let h26 := h3 h25
              -- One of the premise coincides with the conclusion.
              exact h26
        case inr h27 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h28 =>
            -- One of the premise coincides with the conclusion.
            exact h27
          case inr h29 =>
            -- Disjunctions on the left can always be decomposed.
            cases h29
            case inl h30 =>
              -- One of the premise coincides with the conclusion.
              exact h27
            case inr h31 =>
              -- One of the premise coincides with the conclusion.
              exact h27
      case inr h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h33 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h34 : (True ∧ True) := by
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h35 := h3 h34
          -- One of the premise coincides with the conclusion.
          exact h35
        case inr h36 =>
          -- Disjunctions on the left can always be decomposed.
          cases h36
          case inl h37 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h38 : (True ∧ True) := by
              -- Conjunctions on the right can always be decomposed.
              apply And.intro
              -- True on the right can always be proven directly.
              apply True.intro
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h39 := h3 h38
            -- One of the premise coincides with the conclusion.
            exact h39
          case inr h40 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h41 : (True ∧ True) := by
              -- Conjunctions on the right can always be decomposed.
              apply And.intro
              -- True on the right can always be proven directly.
              apply True.intro
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h42 := h3 h41
            -- One of the premise coincides with the conclusion.
            exact h42
  case inr h43 =>
    -- False on the left can always be used.
    apply False.elim h43



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_878695396111103800799488312359 : ((((p1 ∧ (True → (((p4 → False) ∧ ((((p5 ∨ False) → p4) → ((((p1 ∨ p4) → p4) ∧ p3) ∨ p2)) ∧ False)) ∧ p2))) ∧ (True ∨ p3)) → p2) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h14 := h5 h13
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- False on the left can always be used.
    apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315062535935680189135418845594 : (p3 ∨ ((p2 ∨ ((p4 ∧ True) ∧ ((p3 ∧ p2) ∨ True))) → (p1 ∨ ((p4 ∨ True) ∧ ((p4 → ((True → False) → p3)) ∧ (True ∧ (False → p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- False on the left can always be used.
    apply False.elim h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h16
      -- Implications on the right can always be decomposed.
      intro h17
      -- One of the premise coincides with the conclusion.
      exact h14
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h18
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h20
      -- Implications on the right can always be decomposed.
      intro h21
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h22 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h23 := h21 h22
      -- False on the left can always be used.
      apply False.elim h23
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h24
      -- False on the left can always be used.
      apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204450910426411529731280388076 : ((((True ∧ (p2 ∨ False)) ∧ True) ∨ p1) ∨ (p5 → (((p3 ∨ p2) → (p3 ∧ (p2 ∨ (False ∧ ((p2 ∨ (p1 ∨ True)) ∨ (True ∨ p1)))))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232277097877434445120304348364 : (((p2 → p3) → p1) → ((p2 ∨ (((False ∨ ((p2 ∨ p3) ∨ p2)) ∧ p5) ∨ p5)) ∨ (p1 → (((p4 → p5) ∨ (True → (p1 ∧ True))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197304126201843238185798218585 : ((((False ∨ p3) ∧ ((p4 → False) ∨ p3)) → p5) ∨ ((((((((p5 ∧ True) → True) → p5) → (p1 ∨ True)) ∨ p3) → p5) → p1) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53068068795889251461043477749 : (((p1 ∧ ((p4 ∧ ((False ∧ p2) → ((p1 → False) ∨ p1))) → p1)) ∧ ((p2 ∧ p4) → ((p3 ∨ ((p4 → p3) ∧ True)) ∨ (False ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207317071224909908688021231282 : ((((p2 ∨ True) ∧ (p3 ∨ p4)) ∨ p1) → (((((((((p3 → p5) ∨ p3) ∨ (p3 ∧ p4)) ∧ (p3 → p4)) ∧ p1) ∧ p1) ∧ p4) ∨ True) ∨ p2)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253007226162293333329988813185 : ((True ∧ p3) → ((p2 → ((p2 ∨ (p5 ∨ (((p2 ∨ p1) → p4) → ((True ∧ (p4 ∨ False)) → p4)))) → ((p5 ∧ p1) ∨ True))) ∨ (p4 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164920912898879184696194258078 : ((((((False ∨ p4) ∨ (True ∨ ((p4 ∨ ((p4 ∨ False) → p3)) ∧ p2))) ∨ True) ∨ False) → False) ∨ (False → (True ∨ (((p4 → p4) → p1) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612993106176507948016650504119 : (((((((((p2 ∧ ((p3 → (p3 ∨ (p4 ∧ p2))) → (p2 ∨ p1))) → False) ∨ (p4 ∨ (p4 → p3))) → p3) ∧ True) → (p4 ∨ p4)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_148410799479716415362407667890 : (((((p3 ∧ p2) → (((p3 ∧ (p1 ∧ True)) ∧ (p1 → p2)) ∧ True)) ∨ p3) → (((p1 ∧ p2) ∨ p5) ∨ False)) ∨ (p1 ∨ (True → (p4 ∨ True)))) := by
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
theorem thm_5_vars_347518983333650173038762240286 : (p3 → (((p2 → (True ∧ False)) ∧ (p3 ∨ p5)) → (((True ∨ p4) → False) ∨ ((((False ∧ p1) → p1) ∧ (p3 ∨ p2)) ∨ (True → (True ∧ p2)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54426507477212995375867951208 : ((((((True ∧ False) ∧ p3) ∨ (p3 ∨ p5)) ∨ p3) ∨ ((True ∨ (((p2 ∨ ((p5 → True) ∧ p1)) ∧ (p4 → (p5 ∨ p5))) → True)) ∨ p5)) ∨ p5) := by
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
theorem thm_5_vars_624687042817308286378792537217 : ((((p4 ∨ (p5 ∧ (((p4 ∧ True) ∧ ((p4 ∧ (False ∨ (((((p2 ∧ p4) → p3) ∨ False) ∧ (p2 ∧ p2)) ∨ True))) ∨ True)) → False))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200701072126752223409658206518 : ((p2 ∧ ((p1 ∨ False) ∧ (True → (True → False)))) → (p3 ∨ (p4 ∨ ((p4 ∨ (p3 → (p4 → p5))) → ((p5 → p5) → ((True ∧ True) → p5)))))) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_477594305935488376073707282791 : (((((((p1 ∧ p1) → (p3 → p3)) → False) ∧ (p2 ∨ False)) → (((p4 ∨ p2) ∧ p4) ∧ ((p1 ∧ p4) ∨ (p1 ∨ (True ∨ (p3 ∧ p3)))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : ((p1 ∧ p1) → (p3 → p3)) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h14 := h6 h9
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345414257698869230367431299343 : (p3 → ((((True → (p2 ∨ False)) ∧ ((p3 ∨ (p4 ∨ p1)) ∧ ((False ∧ (p1 → p2)) → ((((True → p1) ∨ p1) ∨ p2) ∨ p4)))) → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57773203748845260558253581420 : (((True ∧ (False ∨ p2)) → (((False ∧ p1) ∧ (True → (p4 ∨ ((False ∧ (p2 ∧ p3)) ∧ False)))) ∨ ((p4 ∧ ((True ∨ p3) ∧ p2)) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172834928667123445923634726010 : ((False ∧ ((((((p1 → False) ∨ False) ∧ p2) ∨ ((p5 ∨ True) → False)) ∨ p2) ∧ p1)) ∨ ((False ∧ p3) ∨ (p4 → ((p5 ∨ p2) ∨ (True → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167700975969050362567300049580 : ((((False ∨ (p4 ∨ p1)) → (False ∨ (p2 ∧ ((p4 ∨ False) → False)))) ∧ (False ∨ (p5 ∨ p1))) → (p4 → (((p2 ∧ p3) ∧ p4) ∨ (False ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h8 : (False ∨ (p4 ∨ p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h9 := h3 h8
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h14 : (p4 ∨ False) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h15 := h13 h14
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h17 : (False ∨ (p4 ∨ p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h18 := h3 h17
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
        have h23 : (p4 ∨ False) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h22, we can now drive its conclusion.
        let h24 := h22 h23
        -- False on the left can always be used.
        apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_995699067940027361487321934427 : (((p5 ∧ ((p5 → False) ∧ (((False → (p5 → (False ∨ (((p2 ∨ p1) ∧ ((True → (True ∨ p5)) → (False ∨ True))) → True)))) → p3) → p5))) → False) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50421192330036615882039749700 : (((p3 ∧ ((((False → (p4 ∧ (p5 ∧ p4))) → p3) → (False ∨ ((p3 ∧ p4) ∨ (p3 ∨ True)))) → p1)) ∨ ((False → (False → False)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61188235434487259103373794244 : ((False ∧ ((p2 → p2) ∧ (((p3 ∨ ((p5 ∧ p3) → ((p5 ∨ False) → True))) ∧ (True ∨ p1)) ∧ ((p3 ∨ (p5 → True)) ∧ (p1 ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137528646104306775523280364974 : ((p5 ∧ (p3 ∧ ((((((((True ∨ (p4 → p4)) ∧ p3) ∨ p2) → (p5 ∨ p5)) ∨ (p2 ∧ p5)) ∨ p5) ∨ True) ∧ p5))) ∨ (True ∧ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94155095604036772944364911189 : ((p2 ∧ ((p4 → ((p1 ∨ ((p3 ∧ (((p5 ∨ True) ∧ True) → p3)) ∨ ((p5 ∧ ((True → p4) ∨ False)) ∨ (False ∨ p4)))) → p3)) ∧ p4)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : (p1 ∨ ((p3 ∧ (((p5 ∨ True) ∧ True) → p3)) ∨ ((p5 ∧ ((True → p4) ∨ False)) ∨ (False ∨ p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697006300442307615036237977793 : (((((p2 ∨ ((p2 ∧ (False ∧ p1)) ∨ p4)) ∧ (p2 ∨ (True ∨ True))) ∧ ((False ∧ (False ∨ p4)) → (p2 ∧ (True → (p4 ∧ (p5 ∨ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156774880904882030442704289723 : ((((p5 ∨ p5) → (p1 ∧ ((True → True) ∧ (((p4 ∨ ((False ∧ p3) ∧ p2)) → False) ∧ p3)))) ∧ False) ∨ ((p3 ∨ p2) ∨ ((True → p2) → p2))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60120882497699825129620161029 : (((p3 ∨ p5) → (((((((p5 ∨ p3) ∧ True) → (False ∨ p5)) ∨ p5) ∧ True) ∧ (((False ∧ True) → (False ∧ (p4 ∧ p1))) ∧ p5)) ∨ True)) ∨ p5) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217989008910193757734887694653 : (((p4 ∧ p2) ∧ (False → False)) → (((p3 ∨ p1) ∧ p1) → (((((p4 ∧ False) ∧ ((p2 ∧ (False ∧ p4)) ∧ (True ∧ p5))) ∧ p1) ∨ p3) ∨ p4))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150009733083142641364822932980 : ((p5 ∨ ((((((p4 → False) → p3) ∨ (p2 → (p4 ∧ True))) → p1) → ((p5 → (False ∧ p4)) → p3)) → p2)) ∨ (False → (p5 → (p4 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746462546774633359610266164383 : ((((p2 ∨ p3) → ((((p2 ∧ (((True → p5) ∨ False) ∨ p5)) ∧ (p1 ∧ p5)) → (((p4 ∧ p4) → p1) ∧ (p4 ∧ False))) ∨ (p3 ∨ p2))) ∨ p1) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677557344767549101847323016524 : (((((p5 ∨ ((False → (p5 ∧ ((((p4 ∧ p1) → False) ∧ p3) ∧ (p3 ∨ (p1 ∨ p1))))) → p2)) ∨ p3) ∨ ((p2 → (p5 → p5)) ∧ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59933580714888991793013208990 : (((True ∨ True) → (False ∨ ((((((p4 → ((((p3 ∨ p4) ∨ p4) → p5) → p2)) → p4) → p3) ∨ (p2 ∨ p1)) ∧ (p3 → p5)) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627949495993366593744684724745 : (((((((p2 ∨ ((False ∨ False) ∧ (p1 ∨ False))) ∧ p3) ∨ ((((p3 → p3) → p4) ∧ ((False ∨ p3) → p2)) ∧ (p1 ∨ False))) ∧ p2) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712472522157310008404816017953 : ((((((p4 ∧ True) ∨ p2) ∨ (p2 ∨ p1)) ∨ (((p2 ∨ (((True → p1) → p5) → (p5 ∨ (True ∧ False)))) ∨ False) ∧ ((True ∧ p1) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806049489262248631158654717353 : (((p4 → (((False ∨ p1) ∨ ((p4 → p5) ∧ (((((p4 ∨ p4) ∧ False) ∨ p1) ∨ True) ∨ ((((p2 → p5) ∧ False) → True) → p3)))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311819566916667385962115405095 : (p2 ∨ (p1 ∨ ((p3 ∧ ((p4 ∧ p4) ∨ (p3 ∧ ((True ∧ p2) ∧ (False ∨ (p3 ∨ (((p5 ∨ False) → p5) ∧ p4))))))) ∨ ((p2 ∧ p1) ∨ True)))) := by
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
theorem thm_5_vars_118634458229375477809123714331 : ((p4 ∨ (((False → p2) ∧ p5) → (((False → True) ∧ (((False → False) → p2) ∨ p5)) ∧ (p1 → ((p4 ∨ p3) ∨ (p1 ∨ p2)))))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90992632617696904454504621868 : (((p1 → True) ∧ ((((p1 ∧ p5) ∧ (p5 ∧ ((True ∧ p5) → p1))) ∨ (False ∨ ((p1 ∨ (True → (False → p1))) ∨ (p2 ∨ p2)))) → False)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p1 ∧ p5) ∧ (p5 ∧ ((True ∧ p5) → p1))) ∨ (False ∨ ((p1 ∨ (True → (False → p1))) ∨ (p2 ∨ p2)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644824835614565926704349221067 : ((((p2 ∨ (((p2 ∧ (p3 → (((((p3 ∨ p2) ∧ p3) ∧ p4) ∧ p3) ∧ (p2 ∨ p2)))) ∧ (p2 ∧ (p2 → p1))) ∧ (True ∨ p5))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718727355156915567470235268845 : (((((p5 → True) ∧ (p2 → p3)) ∨ (((False → True) ∨ (p4 ∧ p3)) → (((((p3 ∨ (p1 ∧ p5)) → p1) ∨ (p3 → p1)) ∧ False) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184851935866355216433139540651 : ((((False ∧ p2) ∧ p1) ∧ (p5 ∧ (((True ∧ p5) ∧ True) ∧ p4))) ∨ (False → (p1 ∧ ((True ∧ (p5 ∨ (p5 → (p2 → False)))) ∧ (True ∧ p2))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259374648286729240233115906353 : ((False → p3) → ((True → ((((False → (True ∨ (False ∨ (True → p2)))) ∨ p1) ∧ (p3 → (p2 ∨ (p1 ∧ (p2 ∨ p2))))) → (False ∨ p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119095257437681145789103412463 : ((p1 → ((((((p1 ∧ True) ∨ p5) ∧ p2) → p5) → False) → (p5 ∨ (p2 → (((p5 ∨ False) ∨ p3) ∧ ((True ∧ p3) ∨ False)))))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169042014701721008100987579118 : ((p2 → ((p3 → False) ∨ (p2 ∨ ((((p4 → (p3 → p1)) ∨ True) → (p5 → p5)) ∨ p2)))) → ((p4 ∧ (p4 → (p5 ∨ (p3 ∧ p4)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165936879985605588079124625857 : (((True ∨ p2) ∧ ((((p4 → True) ∧ (p4 ∧ (p4 → (p2 ∧ p3)))) → (p5 → False)) ∨ p2)) ∨ ((((p2 ∨ (False ∧ p2)) ∨ p2) → True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63885051032175662591231497386 : ((False ∨ ((((((p1 ∧ False) ∧ (p2 → (True ∨ p3))) ∧ ((((True ∧ p5) ∨ ((p4 ∨ p4) → p1)) ∧ p4) → p5)) ∨ p5) ∨ p4) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345521649902816804476052760543 : (p3 → (((((p4 ∧ p3) → ((p2 ∧ p4) ∧ (p5 → (p2 → False)))) ∨ p2) → (((p5 ∨ (True ∧ ((p3 ∧ p1) ∧ p3))) ∧ p4) ∧ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117635597952406199000465820753 : ((p3 ∧ ((p5 ∧ (False ∨ (((True ∧ p4) ∧ p3) ∧ (True ∧ (False ∧ (True ∨ ((p2 ∧ p5) ∨ (p1 ∧ (True ∧ p5))))))))) ∨ True)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150340298440082328683854741157 : ((p5 → ((p2 ∨ (((True ∧ p4) ∨ ((((True ∧ p1) ∧ p3) ∨ p4) → p1)) → (p2 ∧ p1))) ∧ (True ∨ False))) ∨ (p3 → (p5 → (p4 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37888631557776487854510928973 : (((((((p3 ∨ ((p4 ∨ p3) → ((False ∨ (p1 ∨ p1)) ∧ ((p1 → (False ∧ p4)) → p4)))) → p2) → p4) → p3) ∧ (p2 ∨ p4)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



