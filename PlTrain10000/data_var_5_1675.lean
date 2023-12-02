variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199269112617087499868876423065 : (((((p1 → (p2 ∧ True)) ∨ False) ∧ p4) ∨ p3) → ((((p4 ∧ p3) ∧ p3) ∧ ((((False ∧ p4) ∨ (p1 ∧ False)) ∧ p5) ∧ True)) ∨ (True ∧ True))) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148142315117204845523595592587 : (((p4 ∧ ((((p1 → (p5 ∧ (p5 ∧ True))) → p2) ∨ p5) → ((False ∨ p3) → (True → p1)))) → (p1 → False)) ∨ (((p4 ∨ p1) → True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134722892821746497361494199600 : ((((p3 → (p5 → False)) ∨ (True ∧ (((p5 ∨ p2) → ((True ∧ True) ∨ (True → (p3 ∨ True)))) ∨ (p2 → True)))) → p5) ∨ ((p4 → True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114301290437879864862904394061 : ((((((True ∧ False) ∨ ((p1 ∨ p3) ∨ p2)) ∧ ((p1 ∨ False) → p3)) → (p5 ∧ (False ∨ p1))) ∧ ((p3 → p1) ∨ (p3 ∨ p3))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49442708130014827717675301261 : ((((((p4 → (p2 ∨ (((p3 ∧ p5) ∨ False) ∧ p1))) ∨ p2) ∨ ((p2 → p2) → (True → (p5 → True)))) ∨ True) → ((p5 → p1) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746314640860606244511434021756 : ((((p2 ∨ True) → ((p2 ∨ (p2 → ((False → p2) ∨ p3))) → (((p5 → p1) ∧ ((p1 ∨ True) ∨ (True ∧ ((False ∧ p2) ∨ p3)))) ∨ True))) ∨ p1) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215949161470799702973580472768 : ((p4 ∨ ((p1 ∨ p2) ∧ False)) ∨ ((p1 ∨ (((True → ((((p5 ∧ (p3 ∨ p4)) ∨ p1) ∨ (p5 ∨ (p1 → p5))) → p5)) → False) ∨ True)) ∨ p1)) := by
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
theorem thm_5_vars_699813270251018207845586197886 : ((((((((True ∨ p2) → p4) ∧ (p2 ∨ True)) → False) → (True → True)) → (p3 → (p2 ∨ ((p3 ∧ ((p3 → p4) ∧ True)) ∧ (p1 ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42054000456260246679424603969 : ((((p2 ∨ False) ∨ (((p1 ∧ p2) ∧ ((((((p5 → p5) → (p1 → p3)) ∨ False) ∧ p5) ∨ p5) ∨ p3)) ∨ (True → (True ∧ False)))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115370047121255675146623463704 : ((((False → ((p2 ∧ (p3 → p5)) ∨ p4)) → p4) ∧ (((((False ∧ ((True ∧ False) → False)) ∨ p2) → p3) → (p5 ∧ p3)) → p1)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58649860827304728788644259387 : (((p1 → p2) ∧ ((p5 ∨ (p5 → (((p1 ∧ p3) ∨ True) ∨ p1))) → ((p2 ∧ p1) ∧ (p2 ∨ (((p3 → True) ∧ (p2 → p3)) ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155220615349102586675992346775 : ((((p5 ∧ p2) ∨ ((False ∧ p5) → (p5 ∧ p3))) ∨ ((False ∧ False) → (p2 → ((True → p3) → p5)))) ∧ ((((p4 → p1) ∨ p1) → p5) ∨ True)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809116797649880242895932902300 : (((p5 → (((((((((p5 ∨ p1) ∨ p5) ∨ p3) → p3) ∧ ((False → p5) ∧ (((p1 ∨ p4) → False) ∨ p1))) ∨ True) ∨ p5) ∧ p5) ∨ p3)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147038611373003363589121783423 : (((((p3 → (p2 → ((p5 → False) ∨ (p4 → p5)))) ∧ (p3 → p5)) ∧ (p5 ∨ ((p4 ∧ False) → p3))) ∧ True) ∨ (False ∨ ((p2 → True) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668859154089320036810962470406 : (((((((p5 ∨ p3) ∨ p4) ∧ (((p5 → p2) → ((p3 ∧ False) ∧ ((p3 ∧ (p3 → False)) ∧ p3))) ∧ p4)) ∨ p1) ∨ ((p3 → True) ∨ False)) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42684496843961792406753890529 : (((p5 ∨ (((p4 ∧ ((p5 ∧ (p1 ∨ p2)) ∨ p4)) ∧ ((p1 → ((((p1 ∧ False) ∨ True) ∧ (True ∧ False)) → p1)) ∨ False)) ∧ p2)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345364964035556421869841973370 : (p3 → ((((p4 ∨ (((p3 → p2) → ((((False → p3) → True) ∨ p3) ∨ p4)) → (True ∨ (False ∨ (p1 → p2))))) → (p2 ∨ p4)) ∨ p2) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2369845898383065230352829467 : (((((p1 ∨ p3) ∧ p4) → ((p5 ∧ p1) ∨ True)) → (True ∧ p3)) ∨ ((((p1 → p3) ∧ (True → (p2 → (True → p3)))) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49274681686991271367413703044 : (((p3 ∧ (((p2 ∨ (((p5 ∧ p1) ∧ False) ∧ ((p4 ∧ (p4 → p1)) → (True ∨ p5)))) ∨ p5) ∧ (p3 → p1))) ∨ ((p1 ∧ p5) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149490937806230961421065524212 : ((p1 ∧ ((((False ∧ ((True → p2) ∧ p3)) → ((p4 ∨ (False → True)) → (True → True))) → (p5 → p2)) ∨ p3)) ∨ ((True ∧ (p3 ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309798388438805339912624954163 : (p2 ∨ (((p2 ∨ ((False ∧ p2) ∨ (p5 ∧ ((p1 ∧ p4) → p1)))) ∧ (p2 ∨ (p4 → ((p1 ∧ p3) ∧ p3)))) ∨ (((p2 ∨ p5) ∧ p1) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608170653741126458299776914616 : (((((((p2 ∨ p2) → ((((True → (p1 ∧ (p3 ∨ p2))) → p5) ∨ (((p4 ∧ (p3 ∨ True)) ∨ p4) → False)) ∨ p5)) ∧ p1) ∨ True) ∨ p3) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_216048192702192745187426376817 : ((p5 ∨ (p2 ∧ (False ∧ True))) ∨ ((True → ((((p5 → (False ∨ p5)) ∧ p1) ∧ p4) ∧ ((p3 ∨ ((p1 ∨ p5) ∧ False)) ∧ (p4 ∧ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57532818674949323059568696664 : (((p5 → (p4 ∨ p2)) ∨ (((False ∧ p5) → ((False ∧ (((p1 → True) → False) → ((False ∨ p2) ∧ False))) ∨ (p5 → (True ∨ False)))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800502914713352769731554324737 : (((p2 → (((((p5 ∧ (p1 ∧ p5)) ∧ p2) → ((False ∧ (((p1 ∨ p5) ∨ p4) → False)) ∧ (False ∨ ((p1 ∧ p3) ∧ False)))) ∨ False) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357276770207959391821741869050 : (p5 → ((p4 ∧ p4) ∨ ((p2 ∨ (False ∨ p1)) → ((((False ∧ p3) ∧ p1) ∨ (p4 ∧ (p1 ∧ p1))) ∨ ((p4 → True) → (True ∨ (p4 → p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48340264101772133042514892426 : (((p2 ∨ (p3 ∧ (((False ∧ (((True ∨ False) ∧ ((p3 ∧ (p4 → (True → p2))) ∨ False)) ∨ (p1 ∨ p4))) → p3) ∨ True))) → (p5 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150067556600816730900044600777 : ((True → ((False ∧ (True → ((p2 ∨ (p3 ∧ p5)) ∧ (p2 ∨ p2)))) ∨ (p4 ∨ (((p5 ∧ p2) → p5) ∨ p4)))) ∨ ((p1 ∨ (p4 ∧ False)) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114415655507970973448067535745 : ((((p2 ∨ p3) ∧ ((((p4 → (((p2 ∧ True) ∨ p3) ∧ p4)) → False) ∧ (True ∧ True)) ∨ p4)) ∨ ((p5 → (p1 ∨ True)) ∧ True)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49085240451267225102389034889 : ((((((p2 ∨ p3) ∨ ((((p3 ∧ (p5 → p5)) ∧ p4) ∨ (p3 → p4)) → p3)) ∨ True) ∧ (p5 ∨ (p1 ∨ True))) ∨ (p3 ∧ (p1 ∨ p5))) ∨ p2) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111675597074735959716648125202 : ((((p4 → (p5 ∨ (((True → True) ∧ ((False ∧ ((p3 → ((False ∧ p1) → p4)) → p1)) ∨ p4)) ∨ (p1 → p5)))) ∨ p4) ∨ p5) ∨ (p4 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336070487494322857000224829520 : (p1 → (((((p3 ∨ ((((p2 ∨ False) → (True ∧ ((False → p3) ∨ (False → (p1 ∧ p4))))) ∨ True) ∨ True)) → (p4 ∨ p2)) ∨ False) ∧ p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148848965511054176834688011118 : ((((True ∨ False) ∨ (p1 → p3)) ∧ (((p4 → ((p5 ∨ p3) ∨ p3)) ∨ p5) ∧ (((p5 ∧ p1) → p5) → p1))) ∨ (((True ∧ p5) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639676349388719626341765816402 : (((((p1 ∨ (p5 ∨ False)) ∧ (p5 ∧ ((((True ∨ (p2 → False)) ∨ p1) → (p4 ∨ (p5 ∨ ((p3 ∨ True) ∧ True)))) ∨ (p4 ∧ False)))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729147366860076957114099144983 : (((((p1 → p2) ∧ True) → (((True ∨ p3) → p1) ∧ ((((False ∨ True) ∧ p3) ∨ (p3 ∨ (p1 → p1))) ∨ ((p1 ∧ (p4 ∧ False)) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156594786995645424640064798579 : (((((((False → (p3 ∨ (p2 → (p4 ∨ (p4 → p2))))) → False) ∨ (p1 ∧ True)) ∨ p5) ∧ p2) ∧ True) ∨ (((p1 ∨ (False → False)) ∧ False) → p1)) := by
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
theorem thm_5_vars_52762657375315811951375033602 : ((((((p3 → False) ∨ False) ∧ (p5 ∨ (p1 → (p3 ∨ (p4 ∨ p3))))) → p2) → (p5 ∧ ((p3 ∧ ((p1 ∧ (p5 → p4)) ∨ p1)) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727061502990827700117762256882 : (((((p4 → p1) → p1) ∨ (((((((p4 → True) ∨ p2) ∧ p2) → p5) ∧ ((True ∧ ((False ∨ p3) ∨ p4)) ∨ (True ∧ p3))) ∧ True) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305180243307159327679880932741 : (p1 ∨ (((p5 ∧ ((p2 ∨ p3) ∧ p5)) ∨ (p4 → (((p3 ∧ (p2 ∧ ((p1 ∧ p4) → p3))) → p1) ∨ True))) ∨ ((p4 ∨ True) ∧ (p1 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_556461280168752616127649432330 : (((p3 ∨ (((p2 ∧ (((p2 ∨ p3) ∧ (False ∨ p5)) ∨ (p3 → (p2 ∧ ((True ∧ False) ∧ p4))))) ∨ (False ∨ (False → p5))) ∨ (p1 → p3))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42386872935370735297943393172 : (((p4 ∧ ((((p3 → ((True ∨ p3) ∧ p4)) ∧ (p1 ∧ True)) ∧ p4) ∧ ((False → p2) → (p5 ∨ (True ∨ ((p5 ∧ p1) → p5)))))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111220135013098576170260955616 : ((((p1 ∧ (p4 ∨ p5)) → (((((p5 → p4) → True) → p2) ∧ p2) ∨ (((p4 → ((p4 ∨ p3) ∨ p4)) → p5) ∧ False))) ∧ p4) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709145942970383191722490850095 : (((((True ∨ (p1 ∨ p3)) → (p5 ∨ (True ∨ False))) → (((p5 ∧ True) → ((p3 ∨ (p2 ∨ p3)) → (((p1 ∨ p1) ∨ p5) ∧ False))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161854453321531073694243172905 : ((True → (True ∨ ((False ∨ (p1 ∨ (((p1 → p3) ∨ (False ∨ ((p4 ∨ p3) ∨ p2))) → True))) ∨ p5))) → (((p2 ∧ p3) ∨ (p2 ∧ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83994757417302894592803172750 : ((((((True ∨ (p5 ∨ p2)) ∧ (p3 ∨ ((p2 ∧ p3) ∧ (p3 → p1)))) ∨ p1) ∨ False) ∧ ((p1 ∧ (p1 → (p5 ∧ p4))) ∧ (p5 → p3))) → p5) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h3.left
          let h11 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h12 := h10.left
          let h13 := h10.right
          -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
          have h14 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h12
          -- We have shown the premise of h13, we can now drive its conclusion.
          let h15 := h13 h14
          -- We need to get the left conjuct of h15 based on <expert-advice>.
          let h16 := h15.left
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- Conjunctions on the left can always be decomposed.
          let h20 := h18.left
          let h21 := h18.right
          -- Conjunctions on the left can always be decomposed.
          let h22 := h3.left
          let h23 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h24 := h22.left
          let h25 := h22.right
          -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
          have h26 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h24
          -- We have shown the premise of h25, we can now drive its conclusion.
          let h27 := h25 h26
          -- We need to get the left conjuct of h27 based on <expert-advice>.
          let h28 := h27.left
          -- One of the premise coincides with the conclusion.
          exact h28
      case inr h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h31 =>
            -- Conjunctions on the left can always be decomposed.
            let h32 := h3.left
            let h33 := h3.right
            -- Conjunctions on the left can always be decomposed.
            let h34 := h32.left
            let h35 := h32.right
            -- One of the premise coincides with the conclusion.
            exact h30
          case inr h36 =>
            -- Conjunctions on the left can always be decomposed.
            let h37 := h36.left
            let h38 := h36.right
            -- Conjunctions on the left can always be decomposed.
            let h39 := h37.left
            let h40 := h37.right
            -- Conjunctions on the left can always be decomposed.
            let h41 := h3.left
            let h42 := h3.right
            -- Conjunctions on the left can always be decomposed.
            let h43 := h41.left
            let h44 := h41.right
            -- One of the premise coincides with the conclusion.
            exact h30
        case inr h45 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h46 =>
            -- Conjunctions on the left can always be decomposed.
            let h47 := h3.left
            let h48 := h3.right
            -- Conjunctions on the left can always be decomposed.
            let h49 := h47.left
            let h50 := h47.right
            -- We want to use the implication h50 based on <expert-advice>. So we show its premise.
            have h51 : p1 := by
              -- One of the premise coincides with the conclusion.
              exact h49
            -- We have shown the premise of h50, we can now drive its conclusion.
            let h52 := h50 h51
            -- We need to get the left conjuct of h52 based on <expert-advice>.
            let h53 := h52.left
            -- One of the premise coincides with the conclusion.
            exact h53
          case inr h54 =>
            -- Conjunctions on the left can always be decomposed.
            let h55 := h54.left
            let h56 := h54.right
            -- Conjunctions on the left can always be decomposed.
            let h57 := h55.left
            let h58 := h55.right
            -- Conjunctions on the left can always be decomposed.
            let h59 := h3.left
            let h60 := h3.right
            -- Conjunctions on the left can always be decomposed.
            let h61 := h59.left
            let h62 := h59.right
            -- We want to use the implication h62 based on <expert-advice>. So we show its premise.
            have h63 : p1 := by
              -- One of the premise coincides with the conclusion.
              exact h61
            -- We have shown the premise of h62, we can now drive its conclusion.
            let h64 := h62 h63
            -- We need to get the left conjuct of h64 based on <expert-advice>.
            let h65 := h64.left
            -- One of the premise coincides with the conclusion.
            exact h65
    case inr h66 =>
      -- Conjunctions on the left can always be decomposed.
      let h67 := h3.left
      let h68 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h69 := h67.left
      let h70 := h67.right
      -- We want to use the implication h70 based on <expert-advice>. So we show its premise.
      have h71 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h69
      -- We have shown the premise of h70, we can now drive its conclusion.
      let h72 := h70 h71
      -- We need to get the left conjuct of h72 based on <expert-advice>.
      let h73 := h72.left
      -- One of the premise coincides with the conclusion.
      exact h73
  case inr h74 =>
    -- False on the left can always be used.
    apply False.elim h74



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138210253369606316718139859689 : ((p2 → ((False ∨ (p3 → ((p4 ∨ (p4 ∨ ((True → True) → (p2 → (((False ∨ False) ∧ False) ∨ p1))))) ∨ p3))) ∧ p2)) ∨ (True ∨ (p5 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158922239178699422392152421927 : ((p1 ∨ (p2 ∨ (p3 ∧ (True ∧ (p3 ∧ (p5 → (p4 ∨ (((p4 → (False ∧ True)) ∧ False) → p4)))))))) ∨ (p5 ∨ (((p2 → p3) → True) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115111657895850571355896746425 : (((((False → (((True → p1) → p1) → False)) ∧ (p1 → False)) → p5) → ((((True ∧ ((p2 ∧ p1) ∧ p5)) ∧ False) → p3) → False)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118605737048681314724273664361 : ((p4 ∨ (((p3 → p2) ∨ (p2 → ((p2 → (p3 ∨ (p2 → (p4 ∧ ((p2 → p4) ∨ p2))))) ∨ p4))) ∨ ((p1 → False) → p1))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66129866728677354864607190942 : ((p5 ∨ (((p5 ∧ ((False → (False ∨ (p5 ∨ p4))) → (True ∧ p1))) ∨ (((False ∧ (p4 ∨ True)) ∨ True) ∧ (p3 → True))) ∧ (True ∨ p5))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148769553404799724004921036004 : ((((p5 ∧ (p5 → (False ∨ p4))) ∨ p1) ∨ ((p2 → p4) ∧ ((p1 ∧ (p4 ∨ False)) → (False → (True ∨ p3))))) ∨ (True ∨ ((p2 ∧ p3) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324021095126001001930904985886 : (p5 ∨ (((p4 ∧ ((p2 ∧ (p4 ∨ p4)) ∨ (p2 ∨ p3))) ∧ (p2 → (p3 ∧ p2))) → ((((False ∨ ((p5 ∨ False) ∨ p3)) → False) → p5) ∨ p1))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h11
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h14 : (False ∨ ((p5 ∨ False) ∨ p3)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h15 := h10 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h17
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h18 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h19 := h3 h18
      -- We need to get the left conjuct of h19 based on <expert-advice>.
      let h20 := h19.left
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h21 : (False ∨ ((p5 ∨ False) ∨ p3)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h20
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h22 := h17 h21
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h25
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h26 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h24
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h27 := h3 h26
      -- We need to get the left conjuct of h27 based on <expert-advice>.
      let h28 := h27.left
      -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
      have h29 : (False ∨ ((p5 ∨ False) ∨ p3)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h28
      -- We have shown the premise of h25, we can now drive its conclusion.
      let h30 := h25 h29
      -- False on the left can always be used.
      apply False.elim h30
    case inr h31 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h32
      -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
      have h33 : (False ∨ ((p5 ∨ False) ∨ p3)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h31
      -- We have shown the premise of h32, we can now drive its conclusion.
      let h34 := h32 h33
      -- False on the left can always be used.
      apply False.elim h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140200457218660450863528366721 : (((((p3 ∧ p3) ∧ p5) → ((((False ∧ p1) ∨ False) ∨ ((True ∧ p1) ∨ (p5 ∨ (p1 ∧ p5)))) ∧ p4)) → (p1 ∧ p2)) → (p4 → (p4 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (((p3 ∧ p3) ∧ p5) → ((((False ∧ p1) ∨ False) ∨ ((True ∧ p1) ∨ (p5 ∨ (p1 ∧ p5)))) ∧ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Conjunctions on the left can always be decomposed.
    let h10 := h5.left
    let h11 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h4
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49124738128568864711020240906 : ((((True ∧ (((p5 ∨ p1) ∧ p5) ∧ (p3 ∨ ((p4 ∧ p4) ∧ p4)))) ∧ (((p5 ∧ False) ∨ p2) → (p4 → p1))) ∨ ((p2 → p4) → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721857482421211291952718414290 : ((((p4 ∨ ((p2 → True) ∧ p1)) → ((p4 ∨ (((((p4 → p1) ∨ p5) ∧ (((p2 ∧ True) ∨ (p3 ∨ False)) → True)) → p2) → p3)) ∨ p1)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205527777351398791354150642049 : (((False ∨ p2) ∧ ((p2 → True) ∧ p5)) ∨ ((p5 ∧ p2) ∨ ((p2 → (False ∧ p4)) → ((False → True) ∧ ((((True ∨ p4) ∨ p4) ∨ p1) ∨ p2))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345084226922540270007551411182 : (p3 → ((((p3 ∧ ((p4 ∨ (p2 ∧ p1)) ∧ (((p1 ∧ False) ∨ p1) ∧ p1))) ∨ True) ∨ ((p1 ∨ (True → p2)) ∨ (p5 ∧ (p2 ∨ p3)))) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115742725205680541641512125489 : ((((p3 ∧ p3) ∨ ((p3 ∧ p5) → p5)) → (((p1 ∨ p5) ∧ (True → (((p1 ∧ p2) → ((p1 → True) ∧ p1)) → p3))) ∨ p1)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740862646788618810927428165901 : ((((p3 ∨ p1) ∨ (((p5 ∨ ((p1 ∧ (True ∧ p4)) ∨ False)) → (False ∧ ((p4 → ((p4 → False) ∧ False)) ∨ (True ∧ (p5 ∨ True))))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329694343724200544306335840302 : (True → ((p4 ∨ p2) → ((p5 ∨ True) ∧ ((((((((p1 ∧ True) ∧ p4) ∨ p2) ∧ (p4 → p2)) ∨ p5) ∧ (p2 ∧ False)) ∨ p5) ∨ (p5 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750728662566072950623264084026 : (((True ∧ ((((False → (((((False ∧ p1) → p3) ∧ p3) → p2) ∨ p1)) ∨ p3) ∨ p3) → (((p2 ∨ p3) ∧ (p3 → p2)) → (p1 ∨ True)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    cases h1
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
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
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111710032462086106786985878395 : (((((p3 ∨ ((p3 → False) ∨ ((p1 ∨ ((p4 ∨ p2) ∧ (p4 → p2))) → p1))) ∨ (p2 ∧ ((p5 → p4) ∧ p2))) → p4) ∨ True) ∨ (p2 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166173092519689124057381132016 : ((False ∧ (False ∨ (p1 → (p4 ∨ ((((p2 ∧ p3) ∨ p5) → p1) ∧ (p2 ∨ (False ∨ p2))))))) ∨ (p4 → ((p4 ∧ (True ∧ (True ∨ False))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41312616236795741175139936617 : ((((((True ∧ p4) ∨ (((True → p4) ∨ ((p4 ∨ p5) ∨ p2)) ∧ p3)) ∨ (False ∧ p1)) ∧ (p2 ∧ ((p2 → (p1 ∧ p4)) → p2))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_932096224366276142352302520194 : ((((((False → p5) ∨ (p3 ∨ (True → p3))) → p2) ∧ (p1 ∨ ((False ∧ (p2 ∧ True)) → ((((p1 → p3) ∧ False) ∨ (p5 ∧ p1)) ∧ p1)))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((False → p5) ∨ (p3 ∨ (True → p3))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : ((False → p5) ∨ (p3 ∨ (True → p3))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h9
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218476013395308273040876184718 : (((True ∨ p4) → (True ∧ p4)) → (((p5 ∨ (p4 ∨ p1)) ∧ p4) → (((True ∧ ((False ∨ p1) ∨ True)) ∨ (p2 → p2)) ∧ ((False ∨ p4) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
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
    case inr h8 =>
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
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130478345461166114396482362521 : (((p3 → (((p1 ∨ (p1 ∧ ((p1 ∨ (p4 ∧ p5)) ∧ p1))) ∨ p1) ∨ (p3 ∨ (p1 → p5)))) ∨ ((True ∧ p5) → True)) ∧ (True ∨ (p4 → p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200300256929036293758111593912 : (((p1 ∧ p2) ∧ ((p3 ∧ p5) ∨ (p4 → p5))) → (((p3 ∨ (((p4 → p2) → (p3 ∧ p5)) ∧ ((p4 ∨ p2) ∧ p5))) ∨ p1) ∨ (p3 ∨ p1))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117236213490655132101080903882 : ((True ∧ (p4 ∧ (((((p4 → ((True ∨ (p5 ∨ p4)) → True)) ∧ (p1 → (p2 ∧ (p4 → p5)))) ∨ (p3 ∨ p4)) ∧ False) ∧ False))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200010001179805822992948327964 : ((((p2 ∧ p5) ∧ (p3 → p3)) → (p4 ∨ p5)) → ((p5 → (p2 ∨ p3)) ∨ ((p2 ∧ (((True → (p3 ∧ p4)) → (True ∧ p3)) → p4)) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179123944015492140957221473080 : ((p1 ∧ (((False → (p1 ∧ (p2 → p1))) ∨ ((p5 ∧ p4) ∧ p4)) → p5)) ∨ ((p4 ∧ p1) → ((p4 ∧ False) ∨ ((p5 ∧ True) ∨ (p3 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322320304090334039141951292777 : (p5 ∨ (((((False ∧ p5) → ((p1 ∨ False) ∧ p3)) ∧ ((p5 ∨ ((p5 → (p2 ∨ (False → (p5 ∧ p3)))) ∨ True)) → p1)) ∧ (True → p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54710644016136711830743118753 : ((((p4 ∨ (p5 → (p3 ∧ p2))) ∨ (p5 → p5)) → (((p4 ∧ (p3 ∨ (p2 → (p5 ∨ p2)))) ∨ p1) ∨ ((p2 ∨ True) ∨ (True ∧ p3)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50934723362705117719524828682 : (((((((p1 → p4) ∨ p1) ∨ ((False ∨ p5) ∨ False)) ∨ True) ∧ ((False ∨ p4) → (True ∧ p4))) ∧ (((p1 ∨ (True ∧ p1)) ∧ p5) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43555683382199065030413175303 : ((((((p3 → ((((p3 → True) → p4) ∧ p2) ∨ ((((False → ((False ∨ True) ∨ False)) → False) ∧ p5) → p4))) → p2) ∧ p2) → p4) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1735486325305543534950589328 : (((p4 ∧ p3) ∨ (p3 ∨ ((p2 → (((p3 ∨ p4) → p2) ∨ p5)) ∨ ((p3 ∨ (p4 → False)) ∧ (p2 ∨ p4))))) ∧ ((p5 ∧ False) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174213385430914701515542668581 : (((((p5 → p4) ∨ ((p3 ∧ p4) ∨ (p2 → p5))) ∨ (p2 ∧ p5)) → (p4 ∨ p5)) → ((((p5 → p2) ∨ ((p1 ∧ True) ∧ p1)) ∨ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37085580831112809658806588956 : (((((((True ∨ p3) → ((p1 ∨ p1) ∧ False)) ∨ (True → (True ∧ ((p4 ∧ (((False ∧ p2) ∧ p5) ∨ True)) ∧ p1)))) ∨ p1) ∧ p4) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38168749726824902352128083619 : (((((((p3 ∧ p4) ∨ (p1 ∨ (p3 ∨ p5))) ∧ False) ∧ (p1 → ((p3 ∨ p5) ∧ (p3 → (False ∧ True))))) ∨ ((False ∨ False) → p5)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116548765001680085873546172403 : (((p1 ∨ True) ∧ (((False ∨ (p2 → ((p1 → (((p3 → p2) → p5) ∧ p3)) ∨ (False ∧ p5)))) ∨ True) ∨ ((p2 → p3) ∨ p3))) ∨ (p2 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150375148838933414959400017093 : (((((p2 ∨ (p3 ∧ (p5 → ((False ∨ (p1 ∨ (p1 ∧ True))) → (True → (p1 ∨ p4)))))) ∧ p3) ∧ p4) ∧ p5) → (((p1 → False) ∧ True) ∨ p3)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340821335705567269284802967262 : (p2 → ((((p1 → ((p5 → (p5 ∨ (((p2 ∨ (False ∧ p4)) → p4) → p3))) → ((p1 ∨ True) → p4))) ∨ (False → p4)) ∨ (p5 ∧ True)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310626545203897857481923367850 : (p2 ∨ (((p5 ∧ p4) ∨ (p2 ∧ True)) ∨ (((((((p5 ∨ (p3 → p5)) ∧ True) ∨ True) ∧ (True ∨ True)) ∧ True) ∨ (p5 ∨ (p5 ∧ p1))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50354464546078111226882439894 : ((((False ∨ (p3 → (True → False))) ∨ (p3 ∧ (((True → (p3 ∨ (p2 → (True → p2)))) → False) ∧ p3))) ∨ (p2 → (False → (p1 ∧ p4)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_914386890858584278780768764333 : ((((((((p3 ∧ (p3 → p5)) ∨ (p5 ∨ True)) ∧ True) ∨ True) ∨ ((p1 ∨ p4) → True)) ∧ (((p2 ∨ ((False ∧ False) ∧ p2)) → True) → False)) → p4) ∧ True) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h11 : ((p2 ∨ ((False ∧ False) ∧ p2)) → True) := by
          -- Implications on the right can always be decomposed.
          intro h12
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h13 := h3 h11
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h16 : ((p2 ∨ ((False ∧ False) ∧ p2)) → True) := by
            -- Implications on the right can always be decomposed.
            intro h17
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h18 := h3 h16
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h20 : ((p2 ∨ ((False ∧ False) ∧ p2)) → True) := by
            -- Implications on the right can always be decomposed.
            intro h21
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h22 := h3 h20
          -- False on the left can always be used.
          apply False.elim h22
    case inr h23 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h24 : ((p2 ∨ ((False ∧ False) ∧ p2)) → True) := by
        -- Implications on the right can always be decomposed.
        intro h25
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h26 := h3 h24
      -- False on the left can always be used.
      apply False.elim h26
  case inr h27 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h28 : ((p2 ∨ ((False ∧ False) ∧ p2)) → True) := by
      -- Implications on the right can always be decomposed.
      intro h29
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h30 := h3 h28
    -- False on the left can always be used.
    apply False.elim h30
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_525609938664121979782167744761 : (((True ∧ (p1 → (p1 → ((((((p4 ∨ (p4 ∨ (p1 → (False → p3)))) ∧ (True ∧ p1)) → p3) ∨ (p1 ∨ p3)) → False) ∨ (p2 ∨ True))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218098722426209498520856942741 : (((False → p2) ∧ (False ∨ p2)) → (p4 → (((((((p3 ∧ p5) → p2) ∧ p4) ∨ p1) → ((p2 → p5) → (p5 ∨ p3))) → (False ∧ False)) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : (((((p3 ∧ p5) → p2) ∧ p4) ∨ p1) → ((p2 → p5) → (p5 ∨ p3))) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h14 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h15 := h10 h14
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h17 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h18 := h10 h17
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h19 := h3 h8
    -- We need to get the left conjuct of h19 based on <expert-advice>.
    let h20 := h19.left
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351940289729892527451733796392 : (p4 → ((((p1 → False) → False) ∧ (p4 ∧ ((p4 → p4) → True))) → ((((p2 ∧ (p1 ∨ False)) ∨ (p5 ∧ p5)) → p2) ∨ (True ∨ (True ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150540769637044916845396811859 : ((((p1 → ((p1 → (p4 ∨ True)) → (p2 → True))) → (((False ∨ True) → (p1 ∧ True)) ∧ (False ∧ p3))) ∧ p2) → ((True → (p5 ∨ p2)) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p1 → ((p1 → (p4 ∨ True)) → (p2 → True))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h5
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2178526108893324354739624223 : ((((((p2 ∧ False) ∨ ((p5 ∨ p3) ∧ p2)) ∧ (False ∧ p2)) ∨ (p3 ∨ p3)) ∨ p4) ∨ (p5 → ((p2 → (p2 ∨ p2)) ∧ (p5 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327851023115883890629802330923 : (True → (((((p3 → (p1 ∨ p2)) ∨ p5) ∧ p4) ∧ ((True ∧ ((True → False) ∨ (p5 → (p5 → True)))) ∧ ((p5 ∨ p4) ∨ False))) ∨ (False → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156700258506490326002930732114 : ((((((True ∨ True) → ((p4 → p4) ∧ p4)) ∧ ((True ∧ p5) ∨ p3)) → (False ∨ (False ∧ p5))) ∧ p5) ∨ ((p1 ∧ (True ∨ p1)) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304691927848214448384310514847 : (p1 ∨ (((p2 ∧ (((p1 ∨ False) → True) → ((True ∨ (p1 → (((p4 ∧ p1) ∧ (True ∨ p4)) ∧ p4))) → (p2 ∧ p4)))) ∨ True) ∨ (p5 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47293955050142829051566422950 : (((((p3 → False) ∧ p4) ∧ (p3 → ((p2 ∧ (((p5 ∨ p5) ∧ p5) ∨ (p5 ∨ p5))) ∨ (True ∧ ((True ∧ p2) ∨ False))))) ∨ (p4 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136922560875992457398915211100 : (((p1 → p3) ∨ ((((((p1 → p1) ∨ ((p4 ∨ p2) ∨ (p4 → p3))) → p2) ∨ (True ∧ (p3 → p4))) ∨ p3) ∨ True)) ∨ ((p4 ∧ False) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207756773283982437648496271348 : (((p1 ∨ ((p4 ∨ p1) ∨ p1)) → p1) → (((((p3 ∨ (p1 ∨ p3)) ∨ (p3 ∨ p5)) ∨ ((True ∨ p4) → (False ∨ True))) ∨ (p5 → p1)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_69384441146453978617110751377 : ((p5 → (p1 → (p1 → (p1 ∧ ((True → ((((p5 → p3) ∧ True) ∨ (p2 → True)) ∧ ((((p5 ∨ p1) ∨ p5) ∨ p3) → True))) → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157160927355350174163378788597 : ((((False ∨ (False ∨ (((p3 ∧ ((p2 ∧ p1) ∧ p2)) ∧ p1) → ((p4 → p1) ∧ p4)))) ∨ p5) → False) ∨ (((p5 → p4) ∨ True) ∧ (p1 → True))) := by
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
theorem thm_5_vars_326252220152937907571352275143 : (p5 ∨ (p3 → ((p5 ∨ True) ∧ ((p5 ∨ True) → ((False ∨ ((p3 → ((True ∨ p4) ∨ p2)) ∧ p2)) ∨ (p3 → (p4 → (p3 ∨ (True ∨ p1))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778709967676111095323563643394 : (((p1 ∨ (p3 ∨ (((True → (False → True)) ∧ p5) ∨ (((False ∧ p5) ∧ p1) ∨ (((p1 ∧ ((False ∨ (p2 ∨ p3)) → p2)) → p2) → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



