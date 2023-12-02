variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231400791580249106590058251912 : (((p1 → p1) ∨ p2) → ((True → (False ∧ p4)) ∨ ((False → (p3 → p3)) → ((p4 → (p5 ∧ (False → p2))) ∨ (((p5 ∧ p1) → False) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149426929084186296494422952768 : ((True ∧ (p2 ∧ (((p2 → (p5 ∧ p2)) ∨ (p1 ∧ ((True ∧ (p2 → (p5 ∨ p3))) ∧ p4))) ∨ (p1 → p3)))) ∨ ((True → (True ∨ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115705140470877447441430028095 : (((((p1 → p3) ∨ (p4 ∨ p5)) ∧ p2) → (((p1 → p5) → False) → (((p3 → (p5 ∧ (p2 → True))) ∧ (p3 ∧ p3)) → p1))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175340884469536695176737513281 : ((p5 ∨ ((((False → p2) → ((True ∧ p2) ∧ (p5 ∧ True))) ∨ (p5 ∨ p1)) ∨ p4)) → ((((p5 → (p1 → p3)) → p4) ∨ (p2 ∨ p3)) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248637652224886226720106056914 : ((p3 ∨ p1) ∨ ((((p2 ∧ (((p2 ∨ False) ∨ (p4 ∧ p1)) ∨ True)) ∧ p3) → (((p4 → False) → p4) ∨ (p2 ∨ p3))) ∨ (p3 → (False → True)))) := by
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
theorem thm_5_vars_110792970704236648046384194182 : (((((p1 ∧ ((False → (p2 ∧ ((True → p2) ∨ True))) ∧ (((p1 → (p2 → p1)) ∨ p1) ∨ (p5 ∨ False)))) → p3) ∨ p2) ∧ p1) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608840623442470854587535998006 : ((((((p5 ∧ ((p2 ∧ p1) ∧ ((False → ((p2 ∧ (p1 ∨ p1)) ∧ p4)) → (p5 → p2)))) ∧ (False ∨ ((True ∨ p2) ∧ False))) ∨ p2) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171591778228321261904270483534 : ((((p2 ∧ (((p5 ∨ p1) ∨ (p5 ∨ True)) → p3)) ∨ (True → (p2 ∨ False))) ∨ False) ∨ (p5 ∨ (p3 → ((((True → p1) ∨ True) → p1) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262427628655514221005784163353 : (True ∧ ((p3 ∧ ((((p5 ∧ p1) ∨ p2) → (p2 → (((False → (False ∨ False)) → p5) ∧ (p4 ∨ ((p5 → p1) → (p4 → p2)))))) → p4)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219412855029912072562037426450 : ((p3 ∨ (p4 → (False ∧ False))) → (((((p1 → False) → (((p5 ∨ ((p3 → p2) → p5)) ∧ True) ∨ True)) → p4) → p5) ∨ ((p4 → p2) → True))) := by
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
theorem thm_5_vars_350044310343219504429406655458 : (p4 → (((p3 ∧ (p4 → (((p5 ∨ (False → True)) ∧ (False → ((p3 ∧ False) ∧ (p4 ∧ ((p3 ∨ p1) → p5))))) ∧ (p1 ∧ p5)))) → p1) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659084451051680527671099685243 : ((((p2 → ((((True ∨ True) ∨ p2) → p5) → (((False ∨ False) → p3) ∧ (((p4 ∨ (p1 → p1)) → False) ∨ (p4 → p3))))) ∨ (p4 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38069462594979330476969357672 : (((((p3 ∧ (((False ∧ p1) ∨ p1) ∧ p4)) → (((p5 ∨ ((p5 ∧ True) ∧ (p3 ∨ p3))) ∧ True) → (True ∧ p5))) → (p3 → p2)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_239149101515389930694822560521 : ((p2 ∨ True) ∧ ((((p4 ∧ (p1 ∨ ((True → (p3 → p1)) → ((p5 ∧ p3) ∧ p1)))) ∧ p3) → ((p2 ∨ (p3 → (False ∧ p4))) ∨ True)) ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243931831400322250405074833269 : ((True ∧ False) ∨ (p4 ∨ ((p4 ∨ (p5 ∨ p4)) ∨ (False → (p3 ∨ ((True ∧ (((p4 ∨ p2) ∧ p1) ∨ ((p5 ∨ p3) ∧ (p2 ∧ p4)))) ∧ p3)))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56920261890732840261506355518 : (((True ∨ (True ∧ p1)) ∧ (((((p3 → ((((False → ((p3 ∨ True) ∧ p2)) ∧ p1) ∨ False) → p4)) ∨ False) → (True → p1)) ∧ p4) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57018513165266758457821668638 : (((False → (p4 → p2)) ∧ ((p2 ∧ (((p4 → True) ∧ p1) ∧ p2)) → (((((p1 → p3) ∧ p2) → p4) ∨ ((p5 ∧ p5) ∧ True)) ∨ p1))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348996405252835766274353727537 : (p3 → (p4 ∨ ((p3 ∨ ((p4 → p3) ∧ (p4 ∨ p2))) ∧ ((p1 ∨ ((p1 ∨ False) ∧ (p2 ∧ (p3 → p3)))) ∨ ((p5 ∧ p5) → (False ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_62271442419925019380093922522 : ((p3 ∧ ((((((p2 ∨ p4) ∨ ((p3 ∨ (p2 ∨ ((p3 ∧ False) → True))) → p4)) → (p5 → (p1 ∨ True))) → p2) ∨ (p2 ∨ p3)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355572359219976857833752691937 : (p5 → (((((p5 → (((True → p1) → (p3 ∨ (True → p2))) ∧ (p4 ∨ p1))) → (p3 ∨ p3)) → False) → ((p5 ∧ True) → p1)) ∨ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134639459362732459233512148867 : (((((p4 ∧ True) ∧ (p5 ∨ ((((False ∨ p4) ∧ p2) → False) → (p2 → p4)))) → (((False ∧ p1) ∧ True) ∨ p3)) → p1) ∨ (True → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154296583905559137350527377215 : (((False ∧ ((p4 ∨ ((p3 ∨ p3) → ((p1 → ((p3 ∨ False) ∧ p2)) → p4))) ∧ (True ∧ p2))) ∨ True) ∧ (False → (True ∧ ((p5 ∧ p5) ∨ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125461218069633560225068536081 : (((True ∨ p3) ∧ (p4 → (((True → (((p2 ∧ False) ∨ False) ∧ p5)) → ((((p5 ∧ p1) → p3) ∧ p2) ∨ (True ∧ p4))) ∨ p1))) → (p5 → p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206774669864988349045808531358 : ((p4 → ((p3 ∧ p3) ∧ (p1 ∧ p5))) ∨ ((p3 ∧ True) ∨ (((p3 ∧ (p3 ∧ p3)) → ((p1 ∧ p1) ∧ ((True → p2) ∨ (p3 → p1)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157188354574327231900833955118 : ((((True → (p5 → (((p1 ∨ (False ∨ (p1 ∧ p5))) ∨ (p1 ∨ p4)) ∨ (p3 ∧ p1)))) → p2) → p5) ∨ ((p4 ∧ (p5 ∨ (p3 ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137629968745709136698530383764 : ((False ∨ ((p3 ∧ (p5 → ((((p2 ∨ False) ∨ p3) ∨ (p5 ∨ (False ∨ (False ∧ p2)))) ∨ (p1 ∨ p4)))) ∧ (p2 ∨ p2))) ∨ ((p4 ∨ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178539792768853258314989848052 : (((True ∨ (p5 ∧ ((p3 → (p4 ∨ p1)) ∧ p4))) → ((p3 → p1) ∧ p1)) ∨ (p5 → ((False ∨ (((p5 → True) → p4) → False)) → (p4 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168676192854232900547880819244 : ((p5 ∧ (((p1 → (p2 ∧ (((p1 → p4) → p3) ∧ p4))) ∧ p3) ∨ (p2 ∨ (p4 ∧ False)))) → ((((p5 ∨ p1) → p2) ∧ False) ∨ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216716168938310842213339772194 : ((((p5 ∧ True) → p5) ∧ p1) → (((((p1 ∧ p4) ∨ (False ∨ (p1 → p5))) → p4) → p3) ∨ (p2 ∨ (p2 → ((False ∧ p2) → (p3 → p5)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178570929666116261278790990347 : (((p1 ∧ (((p1 → p1) ∧ p4) ∨ p3)) ∧ (p2 ∧ ((p2 ∧ p3) ∧ p1))) ∨ (p3 → (False ∨ (p3 ∨ ((True → False) ∨ ((p3 ∨ False) ∨ p2)))))) := by
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
theorem thm_5_vars_137086000243565014592661517853 : ((True ∧ ((False ∨ (((p1 ∨ (p4 ∨ (p4 ∨ (p4 ∨ ((p4 → p2) → ((p5 ∧ False) ∨ p4)))))) → p5) ∧ p2)) ∧ p3)) ∨ ((p1 → p1) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688635554015254529001228840433 : ((((p5 ∨ (((p3 ∨ False) ∧ ((((p5 ∨ p3) → True) ∧ p2) → (p3 → p1))) → p1)) ∧ (p1 → (p5 ∧ (p3 → ((p2 ∨ True) ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728437870198635225832902495125 : ((((p2 → (p4 ∧ p5)) ∨ (True ∧ ((((p1 → (p3 ∨ (p1 → (False → (p5 ∨ p2))))) ∨ (p5 → p3)) → (p1 ∧ p3)) ∨ (p4 → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53647756998642324166703870032 : ((((False ∨ (p3 ∧ p2)) ∨ ((p1 → p1) ∧ (p2 ∧ p3))) ∧ (((p4 ∨ (((p4 → p1) ∧ p5) ∨ p5)) ∧ (p4 ∧ p1)) ∧ (False ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119536473307204865255209532719 : ((p5 → ((p2 ∨ (((((p2 ∨ (((p5 ∨ False) ∨ p5) ∨ p3)) ∧ (True ∧ p1)) ∨ (False ∧ (p5 ∨ p4))) ∨ p4) ∨ p5)) → p2)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173675306932619858778951302547 : ((((((True → p3) → ((p3 → p1) ∧ p2)) → (p4 ∧ (p3 → p2))) ∨ p4) ∨ p2) → (p2 ∨ (((p3 → True) ∨ ((p1 → p3) ∧ p5)) ∧ True))) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50859215988873951549485053067 : (((((((p2 → p4) → (p4 ∧ p1)) ∨ (p1 ∧ True)) ∧ (p4 ∨ ((p5 → p2) → p5))) ∨ False) ∧ ((p4 ∨ p5) → (p2 ∧ (False → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149010019408709181367323323378 : ((((p1 → p2) ∧ p4) ∨ (((p2 ∨ p2) ∧ (True ∧ p5)) ∨ (((p1 ∨ p5) → p1) → (p5 ∨ (p4 ∨ p2))))) ∨ (p5 → ((p1 → True) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299382177166326397073498993670 : (False ∨ (((p1 ∨ p3) → (((p5 ∨ (True ∨ (p1 → True))) → (p1 ∧ True)) ∨ ((p3 ∨ (p2 ∧ p5)) → (p2 → (p5 ∨ (True ∨ False)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705424606585760954741641645216 : (((((True ∨ (p4 → (p4 → (p3 → p4)))) ∨ False) ∧ (((True ∨ p4) → ((p4 ∨ ((p2 → p2) ∧ p1)) ∧ ((True ∧ p2) ∧ p5))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674339726421203715686341117940 : ((((p1 ∨ ((p5 ∨ ((p1 ∧ (((p5 → (False ∧ ((False ∧ p1) ∨ (True → p3)))) → True) → False)) ∧ p3)) ∨ p3)) → ((p5 ∨ p3) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42018017873129764155137431746 : ((((True ∧ p1) ∨ (False ∨ ((p2 ∨ ((p1 → p1) → (((((True → True) → (p5 → True)) ∨ p4) ∧ p4) ∨ (p2 ∧ p4)))) ∨ p1))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784990713610651981963942606943 : (((p3 ∨ (p4 → (p1 → ((((False → p4) ∧ (p4 ∧ (p1 ∨ p2))) ∧ ((p5 → False) ∧ p3)) ∨ ((True → (p2 → (False ∧ p2))) → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178702722007235742551656372532 : (((False ∧ ((p2 ∨ True) ∨ False)) ∨ (False ∨ (((True ∨ p1) → p2) ∨ p1))) ∨ (((p5 ∧ ((p2 ∨ p4) ∧ p2)) ∧ ((True ∨ p4) → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136203964000758472225540622776 : (((p1 ∨ ((p2 → (p2 → p5)) → p1)) ∧ (p3 ∨ ((p5 → ((p3 ∧ (p4 ∨ True)) ∧ (p3 ∧ False))) → (p4 → True)))) ∨ (p2 → (True ∧ True))) := by
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
theorem thm_5_vars_87407086439512788724800286658 : (((True ∨ ((p3 ∧ (True ∨ p3)) ∨ True)) ∧ ((((False ∧ p5) ∨ (True ∧ (p3 → p3))) ∨ ((p2 ∨ p4) ∧ (False → p4))) → (False ∨ p3))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (((False ∧ p5) ∨ (True ∧ (p3 → p3))) ∨ ((p2 ∨ p4) ∧ (False → p4))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h17 : (((False ∧ p5) ∨ (True ∧ (p3 → p3))) ∨ ((p2 ∨ p4) ∧ (False → p4))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h18
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h19 := h3 h17
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- One of the premise coincides with the conclusion.
        exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40912424482237068629791460572 : ((((False ∨ (((((p3 ∨ False) ∧ p4) → False) ∨ (p2 ∧ (p1 ∨ False))) → ((p1 ∧ True) ∧ (p3 → (p2 ∨ True))))) ∧ (p5 → False)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135132462965917822637921002266 : (((p4 ∧ ((p1 ∧ (p4 ∨ (((True ∨ p2) ∨ (p5 → p4)) ∨ (False → (False → True))))) → (True → p5))) ∨ (False → p1)) ∨ (False ∨ (p1 → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738144320245001370063096128948 : ((((False ∧ p1) ∨ (p5 → ((((True → (True ∨ (p5 ∨ True))) → (p3 → ((p1 → True) ∨ (False ∨ p1)))) → p3) ∨ ((p1 ∧ p5) → p1)))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650939042291399844025534137577 : ((((((True ∧ (True → (p2 ∨ p2))) ∨ p5) ∨ ((False ∧ ((((True ∧ p5) ∨ (p1 → p5)) → True) ∧ (p4 → p3))) ∨ p5)) ∧ (p3 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56099644131553646580514895369 : ((((p2 ∨ p5) ∧ (p4 → p1)) ∨ ((p3 → (((True → p5) ∧ (p2 ∨ p5)) ∧ p4)) ∨ (p5 ∨ (p5 ∨ ((p3 ∨ p3) → (True ∧ True)))))) ∨ p3) := by
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
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112077696273960145146510018839 : ((((p2 ∧ p2) ∨ (p5 → (((((p1 ∨ False) ∨ (True → False)) ∨ ((p4 ∨ (p4 ∧ p4)) ∨ False)) ∧ (p1 ∨ False)) ∨ p5))) ∨ p1) ∨ (p5 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_699818206980109920692985861908 : ((((((p1 → ((p4 ∧ True) → p1)) ∧ (p4 → p5)) → (p4 ∨ True)) → (((False → (p2 ∨ True)) → (((p3 ∨ p2) ∧ p2) ∧ p2)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615949783482332810627098460919 : (((((((((p4 ∨ p2) → p1) ∧ ((p2 ∨ False) ∨ (p3 ∧ p3))) ∧ p4) ∨ p3) → ((True → p5) → (((True ∧ True) ∧ p4) ∧ p2))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78280278926108560074259830060 : (((p4 → ((p2 ∨ (p5 ∨ p5)) ∨ (True → ((p4 → (p4 → False)) ∨ (((((p4 ∧ (p3 → p2)) ∧ p5) ∧ p2) ∨ True) ∨ p1))))) → p2) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → ((p2 ∨ (p5 ∨ p5)) ∨ (True → ((p4 → (p4 → False)) ∨ (((((p4 ∧ (p3 → p2)) ∧ p5) ∧ p2) ∨ True) ∨ p1))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151804433419280909452801608355 : ((((((((p4 → False) ∧ p3) ∧ (p3 → p1)) ∨ (p4 ∨ p2)) ∧ p3) → p2) ∧ (p4 ∨ (p3 ∨ (p5 ∧ p1)))) → (p3 → ((p3 → p5) → p5))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h11
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310117319303548205671314570758 : (p2 ∨ ((((False → (p2 → (p4 ∧ p4))) → ((p3 ∨ p5) → (p5 → p4))) → p1) ∨ (((p3 ∨ p5) ∨ p4) ∨ (((p2 ∨ False) ∧ p1) ∨ True)))) := by
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
theorem thm_5_vars_191104555582865831700057007632 : (((True ∧ (p3 ∨ p3)) ∧ (False → (p2 → (p4 ∨ p2)))) ∨ (((p3 → False) → p5) ∨ ((((True ∨ p3) ∧ (p1 ∨ (False → p2))) → p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224568669272775833302543939679 : ((p2 → (p4 ∨ p2)) ∧ ((p2 ∨ ((p5 → p2) ∧ True)) ∨ ((((((True ∧ p2) → p5) ∧ ((True ∨ p2) → p2)) ∨ (p4 → False)) → p4) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301048222382029304061420469717 : (False ∨ ((((((p5 → (p2 → p3)) ∧ p1) → p5) ∨ False) → p3) ∨ (((p4 → p3) ∨ (p4 ∨ (p3 → True))) → (p4 → (True → (p2 ∨ p4)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137015856353273870231214531256 : (((p2 ∨ p2) → (p1 → (p4 ∨ ((p4 ∧ ((p4 ∧ p1) ∧ False)) ∨ ((p1 ∧ p3) ∧ (p1 ∧ (p1 ∧ (p1 ∧ p3)))))))) ∨ (p4 → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133998054805141746805351826801 : ((((((p5 ∨ p3) → (p5 → p3)) → (p5 ∧ ((((p1 → p4) ∨ (p4 ∨ (p5 ∧ p5))) ∨ p1) ∨ True))) ∧ False) ∨ p2) ∨ ((False ∧ True) → p5)) := by
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
theorem thm_5_vars_128546960871392716127044310473 : ((p5 → (p3 → (False ∨ ((p3 ∧ (p2 → ((p5 → p4) ∧ False))) ∨ (p5 → (p1 ∨ (p3 ∧ ((True ∨ (True ∨ True)) ∧ p1)))))))) → (p4 → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166407154281935806551977449315 : ((p1 ∨ (((p2 → ((p4 → ((p4 ∧ p4) ∧ p1)) ∧ p1)) ∨ (False ∧ (p3 → True))) ∧ False)) ∨ ((False → ((False ∧ p2) ∨ p3)) → (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40210168963768835048182837301 : (((((p5 ∨ p1) ∨ (p1 → ((True → (p1 ∨ p4)) ∧ ((p2 → (p3 ∨ (p5 ∧ (p1 ∧ p5)))) ∧ ((p2 → p2) ∨ True))))) ∧ p1) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703745266321341417884652404218 : (((((True ∧ ((False ∨ (p1 ∨ p5)) → (False → p5))) ∧ True) → ((((True ∨ (p2 ∨ p5)) → ((p5 ∧ p3) → p1)) ∧ (p5 ∨ p4)) ∨ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_464413350115218875224154292915 : ((((((p3 ∧ p5) ∨ ((((p3 ∧ (p2 ∨ False)) ∨ p2) → p1) ∧ p1)) ∨ (p5 → False)) → ((((False ∧ (p4 ∨ False)) ∧ p2) ∨ False) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
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
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41044398113198108244895758612 : ((((((p4 ∧ p4) → ((p5 → p2) ∧ p3)) ∨ ((p4 ∧ p3) → (((p4 ∧ False) ∨ (p1 → p5)) ∨ (p2 ∨ True)))) → (p3 ∨ p5)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231871137837446135313613785494 : (((True ∨ p1) → False) → ((((p4 → p3) → ((True ∨ (True ∨ (p5 → p5))) → p3)) ∨ ((p2 ∨ ((False ∨ p5) ∧ (p1 → p5))) → False)) ∨ p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263902590182542172569395178142 : (True ∧ ((p4 ∧ ((p1 ∧ ((p2 ∨ (False → True)) ∨ p2)) ∧ ((False → False) ∧ p3))) ∨ (((p4 ∨ p4) ∨ (((p2 ∨ False) ∨ False) → p2)) ∨ False))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40099904057701485241970236490 : (((((((p1 ∨ ((p2 ∨ p3) ∨ p3)) ∨ (((False ∨ p4) → (False ∧ ((p2 ∨ True) ∧ False))) ∨ p1)) ∨ p1) ∧ (p2 ∧ p3)) ∧ p2) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55989954518265685156652454853 : ((((p2 ∨ (True ∨ True)) ∧ p5) ∨ (((False ∨ (p3 → True)) ∧ (p4 ∧ ((((p3 ∧ (True ∧ p3)) → (p5 → p1)) ∨ p3) → p3))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328524999871714226467999542885 : (True → ((((True → (p1 ∨ p3)) → p2) → ((((p4 ∨ True) → p3) ∨ (True ∨ True)) ∧ True)) ∨ (p1 ∨ (p1 ∧ ((p5 → (p2 → True)) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115397782683159387267593473084 : (((p3 ∧ (((False → p4) ∧ p4) → (p2 → p4))) ∧ (p4 → (((False ∨ p5) ∧ ((p3 ∨ ((p5 ∧ p3) ∧ p1)) ∨ p2)) ∧ p4))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168258243974097543524675476376 : (((p2 ∨ (p3 → p2)) → ((((p1 ∧ (p3 ∧ p2)) → p5) → p5) ∧ (True ∧ (p3 ∧ p4)))) → (p4 → ((True → (False ∧ (True ∧ p4))) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327093238444893539995881179297 : (True → (((p5 → (p3 ∧ p1)) → (((True ∧ (((p4 → (p1 ∧ p5)) ∧ (p3 ∨ (p4 ∨ p4))) ∨ True)) → (p5 → p1)) ∧ (p1 ∧ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323659388073363520806577854831 : (p5 ∨ ((((p5 ∨ ((p5 ∧ ((False ∨ p1) ∨ ((False ∨ p3) → (p5 → True)))) ∨ p5)) ∧ False) ∧ (p2 → p4)) ∨ (((False ∧ True) ∧ False) → p2))) := by
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
theorem thm_5_vars_136088999078223139724705534018 : (((((p5 ∨ ((p5 → p2) ∧ p1)) ∨ p5) ∧ p4) ∨ ((p2 → False) ∨ ((p4 ∨ ((False ∨ p3) ∧ (p2 ∨ True))) ∧ p5))) ∨ ((p4 → p4) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147430908239770502666781956808 : (((((p5 → p3) ∨ False) → ((((False → p4) ∨ (False ∨ p4)) → (p4 → p3)) ∨ (p4 ∧ (p2 ∨ p3)))) ∨ p3) ∨ (((p5 ∨ p3) ∧ p5) → p5)) := by
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
theorem thm_5_vars_314294724227278363398057721624 : (p3 ∨ (((((True → (p5 ∨ (True → p4))) ∧ ((p3 ∧ p3) ∧ (((p3 → True) ∨ False) ∨ (p4 ∧ p4)))) → p2) ∨ False) → (p3 → (p4 → p4)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51086038891268519476701198357 : ((((((p4 ∧ p1) ∨ (True ∧ (((p1 ∧ p5) ∨ ((p1 ∨ p2) ∨ p2)) ∧ True))) ∧ p4) ∧ p1) ∨ ((p1 ∨ (False → (False → p2))) ∨ False)) ∨ p3) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192287742624029248047070181773 : ((((True → p4) ∨ (p4 → ((False ∨ p3) → False))) ∧ p4) → (((True ∨ p5) → p3) ∨ (((p5 ∨ p3) ∨ (True ∨ True)) ∨ ((p3 ∧ p1) → p5)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354065598254251389050973973980 : (p4 → (p4 → (p5 ∨ ((((((p2 ∨ p4) ∧ ((((p3 ∧ True) → p3) ∨ p3) ∨ False)) ∨ p4) → False) ∧ (((False → False) ∧ p5) → p2)) → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (((p2 ∨ p4) ∧ ((((p3 ∧ True) → p3) ∨ p3) ∨ False)) ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354547087342706328102484554661 : (p5 → ((p4 → ((((p1 ∧ ((p5 ∧ p2) → p2)) → ((p3 → (p4 → (True → (p3 ∨ ((p2 ∨ p5) ∨ True))))) ∨ p4)) → p2) ∨ True)) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116627178209692291474314860375 : (((p1 → False) ∧ ((p2 → (p5 → (((p2 → (True → ((p5 → ((p4 → p1) ∨ True)) → True))) ∨ (p1 → False)) → False))) ∨ p1)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147055881524401025937073066719 : ((((p2 → (p5 ∧ ((p3 → True) ∧ (p2 → (True ∧ p3))))) ∨ (((p1 ∨ p2) → (p4 ∨ p1)) → p4)) ∧ p4) ∨ (p5 ∨ ((p4 → p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348127678735900722836845611230 : (p3 → ((p1 ∧ True) → ((((p4 ∧ (False ∨ ((p5 ∨ (((True ∧ p3) ∨ p3) → (False ∨ p4))) ∧ p2))) ∧ p5) → p2) → ((p4 → p2) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42284726586824084353959242544 : (((p1 ∧ (p5 ∨ ((((p5 ∧ ((True ∧ p3) ∨ p4)) ∨ ((p3 ∨ (False ∨ (p3 ∨ True))) → (p5 → (True ∧ p5)))) ∨ p5) ∧ False))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258957226896141565963983148579 : ((True → p3) → ((p5 → ((p1 → (p5 → (True ∧ (False ∧ p5)))) ∨ (p3 ∧ (((p2 ∨ (p2 ∨ p4)) ∧ p4) ∨ (p3 ∧ True))))) ∧ (False ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327023562256349340847348063453 : (True → ((((p5 → ((True ∧ (p1 ∧ ((p3 ∨ False) ∧ p4))) ∨ p4)) ∨ p1) ∧ (((False ∨ (False ∨ (p5 → p3))) ∧ (False → True)) ∧ p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299172694820885429989094502790 : (False ∨ ((((p2 ∧ (p1 → ((((p2 → (((False → p2) ∨ p3) → p5)) → p5) → (p5 ∨ p3)) ∧ (p4 → True)))) ∨ (p5 ∨ True)) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694960212284260240362363591356 : (((((((((False ∨ p4) → p2) ∨ (p3 ∨ (p3 ∨ True))) ∧ False) → True) ∧ p2) → (p1 ∧ (p1 ∨ ((p4 → p4) ∨ ((p3 ∨ True) → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164643981606513127441169451631 : (((p5 ∨ (((False ∧ True) ∨ (p3 ∧ False)) ∨ (p3 ∨ ((p3 → (p1 → p3)) ∨ p1)))) ∧ p5) ∨ ((p5 → p5) ∨ (p4 ∨ ((p2 → p5) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651353013954972696732449560112 : ((((((p5 → p4) → p2) ∨ (p5 → ((False ∧ True) ∨ ((p2 → ((p2 ∨ (True → ((p2 → p5) → False))) → False)) → False)))) ∧ (True ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307120782822336891984813271230 : (p1 ∨ (False ∨ (((False ∧ ((p3 ∨ (p1 ∧ ((p2 ∨ (True ∨ (p1 ∧ p5))) ∧ p5))) → p5)) ∨ (((True ∧ p1) ∨ (p4 ∧ p2)) ∨ p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4054573940808498628657453308 : (p2 ∨ ((p1 ∨ (p1 → p2)) ∨ ((False ∧ (p4 ∧ p1)) ∨ (p2 → (True ∧ ((p4 ∨ True) → (True ∨ (p1 ∨ ((True ∧ p5) → p4))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_615809622096986915029404435995 : ((((((((p4 ∧ p1) ∨ ((p2 ∧ ((p1 ∨ p5) ∨ p2)) ∨ p5)) ∧ p2) → p4) ∨ (((p4 ∨ True) ∨ p4) ∨ ((p2 ∨ p4) → p2))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122651817211682430724997767172 : (((((p3 ∨ (False → (p2 → p4))) ∧ (p2 ∨ ((p4 ∨ p3) ∧ ((p1 ∨ p3) → p3)))) ∧ ((False ∨ True) ∧ False)) → (True ∧ p5)) → (p5 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164882895536254358268292631186 : (((p2 → (((((p5 → False) ∧ (True → (p1 ∧ (p1 → p1)))) ∨ p4) ∧ p3) → p4)) ∨ p2) ∨ ((p5 → ((p4 ∧ (p2 → True)) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307622567729447231231180152861 : (p1 ∨ (p1 → ((False ∨ (True ∨ (p4 ∨ (False ∨ (((True ∧ (p5 → ((False → p4) → p5))) ∨ p5) ∧ (True → p4)))))) → ((False ∨ p1) ∨ p1)))) := by
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
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
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
          cases h11
          case inl h13 =>
            -- Conjunctions on the left can always be decomposed.
            let h14 := h13.left
            let h15 := h13.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1



