variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114624936797452133610106106201 : ((((p3 ∨ ((False ∨ False) → (((p4 ∨ True) ∨ p3) ∨ (p5 → (True ∨ False))))) ∧ p3) ∨ (p5 ∧ ((True ∨ (p5 → p4)) ∧ p1))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233108589739833458431867266520 : ((p4 ∧ (p4 → False)) → ((p5 ∨ (p5 → (p5 ∧ p4))) → ((((p4 ∧ False) ∧ False) ∨ p5) ∧ ((((p4 ∧ (True → p3)) ∨ True) → p4) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- False on the left can always be used.
    apply False.elim h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h1.left
    let h19 := h1.right
    -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
    have h20 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h19, we can now drive its conclusion.
    let h21 := h19 h20
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315653700892679403463907404875 : (p3 ∨ ((p2 ∧ True) ∨ ((False ∧ ((p3 → ((p5 → p2) ∨ p3)) ∧ (False ∧ ((((p1 → (p1 ∨ False)) ∨ (p4 ∧ False)) ∧ True) ∨ p1)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318438731828071211121754841697 : (p4 ∨ (((((True → ((((p4 ∨ p2) ∨ (p3 ∨ (p2 ∧ p2))) ∨ (False ∧ True)) ∨ p2)) ∧ p4) ∨ ((p5 → True) ∨ p5)) ∨ p1) ∧ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683746497987201155911251205820 : ((((((p4 ∨ (((p5 ∧ p3) ∨ (True ∨ True)) ∨ (p3 → ((True ∨ p4) → False)))) ∧ p4) ∨ p3) ∨ ((((p3 → False) ∨ p1) ∨ True) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3975247536870674575728437808 : (p1 ∨ (((p4 ∧ (p4 ∨ False)) ∨ ((((p4 ∨ True) ∨ (p3 ∨ (True ∨ True))) ∧ (((p5 → p5) ∧ p2) ∨ p5)) ∧ False)) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164481785272760750217667722949 : ((((p2 ∨ ((False ∨ (p1 ∨ p4)) ∧ (p4 → (p2 ∧ ((p3 ∨ False) → p5))))) ∨ p4) ∧ True) ∨ (True ∨ ((((True ∧ False) ∧ p2) ∧ True) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810154536717075567239745430411 : (((p5 → ((((((p4 ∧ False) ∨ (p2 ∨ p4)) → p2) ∨ ((p3 ∨ p4) ∨ p3)) ∨ (p1 → False)) ∨ ((p1 → (p3 ∧ (p1 ∨ p5))) → True))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324254155881533041896257872601 : (p5 ∨ ((((True → (p5 ∧ True)) ∧ (p5 → p4)) ∨ p4) ∨ (p2 → (((True ∧ (((((p5 → p4) ∨ p1) → True) ∨ p5) → p1)) ∧ p1) ∨ p2)))) := by
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
theorem thm_5_vars_445293857580431441060928967763 : ((((((p2 → p3) ∨ (p3 ∨ (p5 ∨ ((False → (((p1 → False) ∧ (p3 ∨ p2)) ∧ True)) ∨ (True ∧ p3))))) ∧ p5) → (p1 ∨ (p1 → p5))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- One of the premise coincides with the conclusion.
          exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341743366809523910540751535901 : (p2 → ((True ∧ (p2 → ((p4 ∨ p1) → (((p3 → p1) ∧ False) ∨ ((p1 → (((p1 ∨ False) → p1) → (p4 ∨ p5))) ∧ p1))))) ∨ (p5 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180842491273858946208443706562 : ((((p3 → p3) ∧ p1) ∨ (p2 → ((True ∨ ((p4 ∨ True) ∨ p3)) ∧ p5))) → (((p3 ∧ False) ∧ p4) ∨ ((True ∨ (p4 ∨ (p4 ∧ False))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
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
  case inr h5 =>
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
theorem thm_5_vars_319382331349352259378042694313 : (p4 ∨ ((p4 ∨ (p1 ∨ (((p3 ∧ (((p5 ∧ True) ∨ p3) ∧ p4)) → p1) ∨ False))) ∨ (((((p5 → p3) → p2) ∨ p1) ∧ (p3 ∧ p5)) → p5))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213380042370150304082649495849 : (((True ∨ (True ∨ False)) ∧ p4) ∨ (((p2 ∧ (((False → p4) ∨ p4) → False)) ∨ False) ∨ (((p3 → (True ∧ p1)) → p2) → ((True ∨ p4) ∨ p1)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114897027229651804606638794320 : (((True → ((p2 ∨ ((p4 ∨ ((True → p2) ∧ (p4 ∨ p4))) ∨ True)) ∧ True)) ∨ (((p5 ∧ True) → ((True ∨ p4) ∧ p5)) ∧ p1)) ∨ (p4 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344761274526215991797626513565 : (p2 → (p3 → (p1 → (((((((((p2 → ((p4 ∧ p1) → False)) ∨ p4) → p1) → True) ∨ p1) → (p5 ∧ p2)) ∧ p4) → p3) → (p5 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590993626255929900799410316142 : (((((p2 → (p4 → (p5 → ((False ∨ ((p5 ∧ (((p1 ∧ p4) ∨ (p5 ∨ (p1 ∧ False))) → False)) ∧ True)) ∧ (True → p3))))) → False) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344860960854162072729710329194 : (p2 → (p5 → ((((p1 ∧ p1) ∨ p1) ∧ p4) ∨ (p4 ∨ ((False ∨ (((p3 → True) ∨ (p3 → True)) → False)) → (((False ∧ p4) → p5) ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357444595469675409756054485806 : (p5 → ((True → p3) → (((((p2 ∨ False) → p1) ∧ p1) → p1) → (p4 → ((p3 → ((True ∧ True) → (p3 → ((p2 ∧ True) ∨ p2)))) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43745658662091700955893950768 : (((((p2 → p2) → ((((p3 ∧ ((p5 ∨ ((p1 ∨ False) ∧ True)) → (p5 ∧ p1))) ∨ p2) ∧ (p4 ∨ p3)) ∧ (p2 → p4))) → True) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137777960181758384996362081849 : ((p2 ∨ (((p5 → p4) ∧ ((p4 → p1) → p3)) ∨ ((False ∨ ((p3 ∧ (p3 ∧ (p2 → (True ∧ True)))) → False)) ∨ p2))) ∨ ((p4 ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115834290906604313411270794226 : (((False ∧ ((p2 → p5) ∧ p2)) ∧ ((p5 ∧ (((True ∧ (p3 ∧ p2)) ∧ p5) ∨ p3)) → ((p4 ∨ ((True ∧ p1) ∨ p3)) ∨ p5))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_816078649994907283577626453350 : (((((((p2 ∧ (False ∨ (((p5 ∧ (True → (((True → ((p1 ∨ False) → p3)) ∨ p2) → p1))) ∧ p1) → p4))) → False) → p4) → False) ∧ p4) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p2 ∧ (False ∨ (((p5 ∧ (True → (((True → ((p1 ∨ False) → p3)) ∨ p2) → p1))) ∧ p1) → p4))) → False) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159475212025019614505486612463 : ((((p5 ∨ (p5 → ((p3 ∧ p4) ∨ p1))) ∨ (p3 ∨ (p4 → (((p5 ∨ p2) ∧ p1) ∨ False)))) ∧ True) → (p2 → ((p3 ∧ (True ∧ p4)) ∨ p2))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146972572554553125927145766671 : (((((((p2 ∧ ((p1 ∧ False) ∨ p4)) ∨ p4) ∧ (p2 ∧ (True → (False → True)))) ∧ (False → p2)) → p3) ∧ p4) ∨ (((p5 ∨ True) ∨ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_381531425085267778378515658431 : (((((((p5 → ((p2 → ((p5 → ((((p4 ∨ p3) ∧ p5) ∧ (True ∧ False)) ∧ (p5 → p4))) ∧ p4)) → False)) ∧ p5) ∧ p2) ∨ True) ∨ False) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41213571631175742731136490395 : (((((((p4 ∨ (((p1 ∧ p4) → (p4 ∧ ((p4 ∧ False) ∨ p5))) ∨ False)) ∧ p1) ∧ p2) ∨ True) ∧ (((p1 ∨ p5) → True) ∨ p2)) ∨ p3) ∨ p3) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323512201200539759771378236209 : (p5 ∨ (((p1 → False) ∨ (((((p5 ∨ (((p2 ∨ p4) ∨ p4) ∨ ((p2 ∧ p4) → p4))) ∧ p4) ∨ p3) → p1) → p5)) ∨ ((p1 ∨ True) ∨ p1))) := by
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
theorem thm_5_vars_54572318574717757884830750214 : (((False ∨ (((p4 ∧ (p2 ∧ p1)) ∨ p3) → p1)) ∨ ((False → ((((False → (True → p1)) ∨ (p4 ∧ True)) ∨ p1) → (p3 ∨ p5))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191776127266412634793570726174 : ((p1 ∨ ((p3 → (p3 ∧ p2)) → ((p4 ∨ False) ∧ p2))) ∨ ((p2 → True) ∨ ((p5 → (((p4 → (p4 ∨ True)) ∧ p3) ∧ p5)) ∧ (p3 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51295007375916906815775965989 : (((p5 ∧ (p1 ∨ ((True ∧ (p4 ∧ p3)) ∨ (p5 ∧ (False ∧ ((True ∨ (p3 ∨ p5)) ∨ p3)))))) ∨ (((p2 ∨ p2) ∨ p2) → (p3 → p3))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205919266562807679574915186482 : ((False ∧ ((p4 ∨ (p5 ∧ p2)) ∧ False)) ∨ (((((p1 → (p1 ∧ ((p2 ∨ (p1 → ((True ∨ p3) → p1))) → False))) ∧ p3) → p2) ∧ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249029685243715774294182047034 : ((p4 ∨ False) ∨ (False ∨ (((p2 ∨ ((((p4 ∨ p2) ∧ p5) → ((p4 ∧ p5) ∧ (p3 ∨ (p4 ∨ p1)))) ∧ p5)) ∧ (False → p1)) → (p3 ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749911635319723680123414706290 : (((True ∧ (((((p1 ∧ (True ∨ ((p4 → ((False ∨ p1) ∧ p4)) → False))) ∧ p3) ∧ ((False → ((p4 ∨ p5) → p2)) ∧ p1)) ∨ p5) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191086354129415750282459773518 : ((((False ∧ False) ∨ p5) ∧ (False ∧ (p3 ∧ (p2 ∨ p2)))) ∨ (p2 ∨ ((((False ∨ (p2 → (p2 ∧ (p3 ∧ p5)))) ∧ False) ∨ (True ∨ p2)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_65229414550021443852052715324 : ((p3 ∨ ((p2 ∨ (((p1 → p4) ∨ (True ∧ (p5 → True))) → (((True ∧ (p3 → (p1 ∧ p3))) → (p1 → (p5 ∧ False))) → p5))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66034695554884448042142855209 : ((p5 ∨ (((p5 → p1) → (((False ∨ ((((p5 ∨ p4) → (p3 → True)) → True) → (False → p3))) ∨ ((p2 → p2) ∨ p5)) ∧ p5)) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_942816954961267063587576522135 : (((((p5 → (False ∨ p5)) → p3) ∧ (((p4 ∧ (p2 ∧ p3)) → p2) → (((p4 ∨ (p4 ∧ ((p1 → p5) ∨ p2))) ∧ (p2 ∨ p5)) → True))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p5 → (False ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158242320532118724640928173945 : ((((p5 ∨ p4) ∧ p4) ∨ (p3 ∧ (((((p1 ∧ p1) ∧ (False → False)) ∧ (p2 ∧ p4)) ∨ p3) ∧ p4))) ∨ (p1 → ((True → (False ∧ p5)) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340133932181039837146467424175 : (p1 → (p3 → (p2 ∨ (p5 → ((False ∧ ((((True → p2) ∨ (p4 ∨ p2)) ∨ (((p4 ∨ p4) ∨ (True ∧ p3)) ∨ p5)) ∧ p3)) ∨ (p5 ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111379805322279255413695851584 : (((False ∨ (((p1 → (p1 → False)) ∨ ((p3 ∧ (p4 ∨ (p2 → False))) → ((p5 ∧ True) ∨ (p5 → (True → p2))))) ∧ True)) ∧ p2) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179119194160569114250148347881 : ((p1 ∧ ((p5 ∨ (True ∧ (False ∧ ((p2 ∧ p2) ∨ (True → p1))))) ∧ p4)) ∨ ((False ∧ (True ∨ ((p4 ∨ ((False ∨ p3) → p4)) → p3))) → p1)) := by
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
theorem thm_5_vars_51291683059957233807221326557 : (((p4 ∧ (False → (((p1 → p4) ∨ ((p5 ∨ p2) ∨ (p4 → (p3 → (p1 ∨ False))))) ∨ False))) ∨ ((True ∨ ((p3 → p3) ∨ p3)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114257724897730532992836023012 : (((p3 → (((p1 ∧ (((False → False) → ((p3 ∧ (False ∧ p1)) ∧ p3)) ∧ p1)) ∨ p1) → (p5 → True))) → ((True → p2) → p1)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193618226698339990467105125230 : ((True ∧ ((p1 ∧ (((p1 ∨ False) ∧ False) ∨ False)) → p1)) → (p5 ∨ (((((True ∧ p4) ∧ p2) ∨ ((p1 ∨ p2) ∨ False)) ∨ p5) ∨ (False → p2)))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190400333170019043801793310494 : (((p3 ∧ ((p4 ∧ (p1 → False)) ∨ (p3 ∧ p1))) ∨ True) ∨ (((False ∨ p4) ∨ (False ∧ p2)) → (False ∧ (p2 ∨ (False → ((p5 ∧ False) ∧ p1)))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328561582793155180631221975601 : (True → (((p2 ∧ p3) → (((((p3 → (p5 ∧ True)) → p5) ∧ (p3 ∨ p4)) ∧ p1) ∧ p1)) → ((p4 ∨ False) → (p5 → (p1 ∨ (p1 → True)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115068842255393083174703475882 : (((((p4 → p2) → p2) ∨ (((True → (p3 ∧ True)) → p4) ∧ True)) ∨ ((p4 ∨ p3) ∨ (True → ((p5 → False) → (True ∧ True))))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60821279958726468218728377806 : ((True ∧ (p5 ∧ ((((((((p3 ∨ p1) → ((p1 → (p4 ∧ p2)) ∧ p3)) ∧ p1) ∨ ((True ∨ p3) → p3)) ∨ p2) ∨ p2) ∧ p2) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694120314549009082450067650123 : (((((p1 → (p5 ∨ ((p5 → True) → (p3 ∨ p5)))) → (p5 ∧ (p5 → p5))) ∨ (p4 ∧ (((p3 ∨ (False ∨ True)) → (p5 ∧ False)) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630861131150192981452247998311 : (((((((((False ∧ p2) ∨ ((False → p1) ∧ p5)) ∧ (False ∨ ((p3 ∧ p4) ∧ (False → (False → p1))))) ∨ (False → False)) ∧ p2) → p1) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355528188582358772369102975758 : (p5 → ((((((True ∨ ((False → (p1 ∨ (p3 ∨ ((p5 ∧ (p2 → p5)) → False)))) ∧ p3)) ∧ (True ∧ p3)) ∨ p2) → p1) ∧ p5) ∨ (True ∧ True))) := by
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
theorem thm_5_vars_64909996572632816231675695735 : ((p2 ∨ ((((p5 ∨ ((True → p5) ∧ (p1 ∧ (p2 → p5)))) ∧ (((p3 ∧ p4) → p5) → p5)) ∧ p1) → ((False ∨ (p4 → p5)) ∨ False))) ∨ p3) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h15 := h9 h14
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201213661360139500226273842347 : ((p2 → ((p4 → (False ∨ (p3 → True))) ∨ p4)) → (((((((p2 → False) ∨ True) ∨ p2) → p5) → (p2 → (p3 → p5))) ∨ (False ∨ p3)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (((p2 → False) ∨ True) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141768085679786676187762616067 : (((p4 → False) ∧ (p1 → (((p5 ∧ (((p4 → p2) → p5) ∧ (p5 ∧ ((False ∨ p3) → p2)))) ∨ (False → p4)) ∧ p5))) → (True ∧ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227705769670639638102627681156 : ((p1 ∧ (p2 ∧ p1)) ∨ (False ∨ ((p4 ∧ p3) ∨ (p1 → ((p3 ∨ (p2 ∧ (p3 → (True ∨ (((p2 ∨ p3) ∧ True) ∧ p5))))) ∨ (p1 ∧ True)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117147848853898274449963120266 : ((True ∧ (((((((p3 ∧ (p1 → (p2 ∨ p1))) ∧ (True → p4)) ∨ p1) ∨ p5) ∨ False) ∧ (p5 → ((p1 ∨ p5) → p2))) ∧ p1)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694429496965364958642774669040 : (((((True → p4) ∨ (((((p1 ∨ (p4 ∧ p3)) → p5) ∨ True) ∨ p2) → p5)) ∨ ((((p1 → False) ∨ False) ∧ p5) ∧ ((p5 ∧ p3) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205852948097533570491547605826 : (((p3 → p3) → (False ∧ (p3 ∧ p5))) ∨ ((p5 ∧ (p5 ∧ (((True ∨ p3) → p4) ∧ (p1 ∧ (p5 → (((p5 → p1) ∧ p2) ∨ p5)))))) → p4)) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h10 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h11 := h6 h10
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248711084716137486569693773752 : ((p3 ∨ p2) ∨ ((p1 ∧ (p2 ∧ (p1 ∨ p3))) ∨ (((((p2 → (p2 ∧ ((p5 ∧ (p1 → True)) ∧ p5))) ∨ (True → p5)) ∧ True) ∧ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172919063441601979222418097673 : ((p2 ∧ (False ∨ ((p2 ∧ (((False → (p2 ∨ p5)) → p2) ∧ p4)) ∧ (p2 → True)))) ∨ ((((((p5 ∨ False) → p1) → False) → p2) → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52576350477040957464179297211 : (((((((False ∨ p1) → p1) → (True → (True → p4))) ∨ p5) → (p3 ∧ p5)) ∨ (p5 ∧ ((((p1 ∧ p2) → p4) ∨ p2) ∧ (p1 ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178525306808207066937675383901 : (((((p4 → (p4 ∧ p3)) → p2) → (False → p3)) → ((True → p2) ∧ p5)) ∨ ((p5 → False) ∨ ((p1 → True) ∨ ((True ∨ (p1 ∨ True)) ∨ p4)))) := by
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
theorem thm_5_vars_313282258210635814954072789234 : (p3 ∨ ((p3 ∧ (((p1 → (p4 → p2)) ∨ (p1 → ((p2 → p1) ∧ (p4 ∨ (p5 → p1))))) ∧ ((((p4 ∧ p3) ∨ True) ∧ False) ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42703087759549804019029021026 : (((p5 ∨ ((((p1 ∨ p3) ∨ ((p3 → p5) ∨ p3)) → p5) ∨ ((((p4 ∧ p1) ∨ ((p1 ∧ (p2 ∧ p5)) → p1)) → False) ∧ p5))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218575407008906913531569975184 : (((p1 → p4) → (p2 ∧ p2)) → ((p4 ∨ (p3 → ((((p2 ∨ (p1 → False)) ∧ p5) ∨ True) ∨ (p4 → False)))) ∧ (p3 → (False → (p4 ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151320136201785658881686060052 : (((p5 ∨ (((False → ((False ∧ (p1 ∧ p3)) → (p4 ∨ p5))) ∨ p2) → ((True ∨ (p4 → p4)) ∧ True))) → False) → ((p4 ∧ True) ∧ (p5 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ (((False → ((False ∧ (p1 ∧ p3)) → (p4 ∨ p5))) ∨ p2) → ((True ∨ (p4 → p4)) ∧ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p5 ∨ (((False → ((False ∧ (p1 ∧ p3)) → (p4 ∨ p5))) ∨ p2) → ((True ∨ (p4 → p4)) ∧ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h7
  -- False on the left can always be used.
  apply False.elim h11
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h12 : (p5 ∨ (((False → ((False ∧ (p1 ∧ p3)) → (p4 ∨ p5))) ∨ p2) → ((True ∨ (p4 → p4)) ∧ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h12
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675340354212665353119746511036 : ((((((((p4 → (((p4 ∧ p3) ∧ False) ∧ p4)) ∧ ((False ∨ p3) ∧ p1)) ∨ (p3 ∨ p3)) → True) → p2) ∧ ((p4 → (True ∨ p2)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44322018339336842829278306907 : (((((p4 → p4) ∨ (False ∧ ((p2 → (p3 ∨ (p5 → p3))) → (p3 ∨ (p3 ∨ p1))))) ∨ ((p5 ∨ p3) ∧ (p5 → (p3 ∧ p1)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308680948324780108839014677291 : (p2 ∨ ((False ∨ ((((False ∨ p1) ∨ (p4 ∨ ((((p2 ∨ p4) ∧ ((p3 ∨ p3) ∨ True)) ∨ p3) → (False ∨ p3)))) ∧ p5) ∨ (p2 ∧ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704172700535960891363807189553 : (((((((False ∧ (p5 → p1)) ∧ True) → p2) ∨ (p5 ∨ p2)) → ((p3 ∧ p2) → ((p3 → (p4 ∨ (False ∨ (p2 ∧ p4)))) → (p4 ∧ True)))) ∨ p2) ∧ True) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- One of the premise coincides with the conclusion.
        exact h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h17 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h18 := h3 h17
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- One of the premise coincides with the conclusion.
          exact h24
    case inr h25 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h26 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h27 := h3 h26
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- One of the premise coincides with the conclusion.
        exact h28
      case inr h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- False on the left can always be used.
          apply False.elim h30
        case inr h31 =>
          -- Conjunctions on the left can always be decomposed.
          let h32 := h31.left
          let h33 := h31.right
          -- One of the premise coincides with the conclusion.
          exact h33
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60183743947855944133050714620 : (((p5 ∨ p2) → (((((p2 ∨ p3) ∧ (((p5 ∨ False) ∨ ((p4 → True) → p2)) → True)) → p5) ∨ ((p2 ∨ p1) ∨ p5)) ∨ (p3 ∨ p3))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50267474778555195306606176102 : ((((((p3 → p5) → p3) ∨ (((p4 ∧ (p4 ∨ (False ∧ p4))) → (p5 ∧ p1)) → p1)) ∧ (p5 → p5)) ∨ (p4 ∨ ((p3 → p4) ∨ True))) ∨ p1) := by
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
theorem thm_5_vars_137849604244704439145206889705 : ((p3 ∨ (((p2 ∨ p2) ∨ p2) → ((False → p3) ∧ (((p5 → (p3 ∧ (True ∧ (p2 ∧ (p4 → p5))))) ∧ p4) ∧ p2)))) ∨ (p2 → (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46816034064340865634134482794 : ((((((((False ∧ ((p1 ∧ p5) → (p1 ∧ p4))) ∧ p4) ∨ (((p1 → False) ∨ (p3 ∧ p2)) → p1)) → p3) → False) ∧ p2) ∨ (False → p4)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44890221021033255955720132003 : (((((p3 ∨ p5) → p5) → (False → ((False ∧ (p1 → ((((p4 ∧ True) ∨ (p5 ∧ (p2 ∧ False))) → p2) ∧ p2))) ∧ (p1 → True)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684161674084252698317169473455 : ((((((p2 ∨ ((p1 ∨ (p1 ∧ p1)) ∧ p5)) ∨ ((False ∧ True) → (True ∧ p1))) ∨ (p1 → p3)) ∨ (False ∧ (p2 ∨ (p1 ∧ (p2 ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172822520905500772395766014877 : ((True ∧ ((True ∨ (True ∨ p4)) → ((p2 ∨ ((p4 ∨ p1) ∨ (False ∧ p4))) ∧ True))) ∨ ((((p2 ∧ p2) ∧ p1) → ((p3 ∧ p1) → True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49229774007271275441570485491 : ((((p3 ∨ p1) ∨ ((p5 ∨ (((p5 ∨ p5) ∨ p2) ∧ True)) ∧ ((p2 ∨ True) ∨ (p2 ∨ (p1 → (p5 ∨ p2)))))) ∨ (p3 ∧ (p3 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41692479619109092620973520462 : (((((p5 ∨ (p2 → (True → p5))) ∧ p2) → ((p5 ∨ (p1 ∨ (((p2 ∨ (p1 → (p1 ∧ False))) ∧ p2) → p1))) ∧ (p3 → True))) ∨ p1) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134828820279162327781961210902 : (((p1 ∨ (p4 ∧ ((p4 ∨ (p4 ∨ p4)) ∧ (((False ∧ p3) → ((True ∨ (p1 ∧ (True ∧ False))) ∨ p5)) → p4)))) → p5) ∨ ((p4 → p4) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336211659377226215500448908454 : (p1 → (((((p1 ∨ ((p1 ∨ p2) ∧ True)) ∨ p2) → (((p3 ∨ p3) ∧ (((p5 ∨ p4) ∨ p4) ∨ (p3 ∨ p5))) ∨ p2)) → (p1 → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55967718043638045179953847247 : (((((False ∨ p4) ∨ p1) ∧ p2) ∨ (((p5 ∨ p4) → ((False ∧ ((True ∨ False) → p4)) ∨ p4)) ∨ (p2 ∨ ((p2 ∨ False) ∨ (p2 ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313926437680868682270457003701 : (p3 ∨ ((((p4 → False) → ((((p1 → p3) ∧ p4) ∧ ((p3 ∨ (((False ∧ False) → False) ∨ (p3 ∨ p3))) ∧ p3)) ∧ p3)) ∧ p1) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114562123451254465144143961097 : (((((p5 → (True ∧ p5)) → ((p3 ∨ ((True → (p4 → False)) → p2)) ∨ p5)) → p4) ∧ (True ∨ ((p1 ∧ p1) → (p5 ∨ p5)))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50272586512746734037570147314 : ((((((p2 ∨ (True → p5)) → ((True ∨ (p5 ∧ (p3 → True))) → (p3 ∧ p4))) ∨ p2) ∨ (p3 ∨ p5)) ∨ (p2 ∨ ((p3 ∧ p5) → p5))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263147903317908003956585211384 : (True ∧ (((p5 ∧ p2) → (((p1 → p2) ∨ ((False ∧ (((p1 ∧ (p3 ∨ p3)) → p4) → p2)) ∨ ((p1 ∧ p3) → p4))) → p3)) ∨ (True ∨ False))) := by
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
theorem thm_5_vars_120033759317146009932324609116 : (((((p3 ∨ ((p4 ∨ (p3 → p1)) ∧ (p5 ∧ p1))) ∧ p4) ∨ ((p1 → p2) ∨ (p2 ∧ ((p4 → (p1 ∧ p5)) → False)))) ∧ p3) → (p1 ∨ p3)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h10.left
        let h13 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h10.left
        let h16 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117458908966253226926526565000 : ((p1 ∧ ((p3 ∧ False) ∨ (p3 ∧ (True ∧ (((False → (p2 → ((((False → p5) ∧ False) → True) → (p4 ∨ p2)))) → p2) ∨ p4))))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147441045847365712986788390657 : ((((False → p1) ∧ (((((False → p2) → (True ∨ p1)) → (p4 ∨ (p5 → p2))) → p1) → (p2 ∨ p4))) ∨ p3) ∨ ((False ∨ p2) → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161073187623390774874227012752 : (((p5 → (p2 ∨ p3)) → ((((p1 ∧ ((p2 ∨ True) → (False → True))) ∨ p3) ∧ (p4 ∨ p2)) ∧ False)) → (p5 ∨ (p2 → ((p2 ∨ p2) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p5 → (p2 ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611499012105759739030188253519 : (((((p4 ∧ (((p1 ∧ (p2 ∨ p4)) ∨ (((((p5 ∧ p1) ∨ (p2 ∧ p4)) ∧ (p3 → p2)) ∧ p5) → p4)) → (False → p5))) → p1) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245185294929500320862280071237 : ((p2 ∧ False) ∨ (((p2 ∧ (((p3 ∧ p5) → False) ∧ p4)) ∧ p4) ∨ ((((p4 → p5) ∨ ((p5 → (p2 → p4)) ∨ (p1 → True))) ∨ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200164122329263252377093593423 : ((((p5 → False) ∨ p5) ∨ ((p1 ∨ p1) ∨ p3)) → ((((False → p2) → ((False ∧ False) ∨ (True ∨ (p4 ∨ (p1 → p2))))) ∨ p4) ∧ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h10
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h12
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h14
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- Implications on the right can always be decomposed.
  intro h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299129833103909323516349036023 : (False ∨ ((((((False → (False → (p4 → p5))) ∧ p1) → (p3 → (((p5 ∧ True) → (False → ((p2 ∨ p4) → p3))) → True))) → p4) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9870002572377071768262783878 : (((False ∧ (((p5 → (p1 ∨ (p4 ∨ p1))) ∧ p1) ∧ ((p3 → ((p3 → (p3 → p5)) ∨ ((p5 ∧ p4) → p5))) ∧ (True → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173196374477745308387655970614 : ((p5 ∨ (((p5 ∨ p2) ∧ (p5 ∨ (p2 ∧ ((p3 ∨ False) ∧ (p1 ∧ False))))) ∧ p4)) ∨ (((True ∨ p1) ∨ ((False ∧ (p2 ∨ p1)) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198695284490876970003765972333 : ((p4 ∨ (p4 ∨ ((True → p1) → (p3 ∨ p5)))) ∨ (True ∧ ((p4 ∨ (((p3 ∧ True) ∨ p4) → p2)) → ((p1 ∧ True) ∨ ((p4 ∧ p2) → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157202931839465993340293097716 : (((((p4 ∧ p1) → (((p1 ∧ (True → p3)) → p4) ∧ (False ∧ (p1 ∨ p3)))) ∨ (p5 ∧ p1)) → False) ∨ ((p3 → ((p1 ∨ True) → p3)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_809452047493228652428428809065 : (((p5 → ((((False ∧ (((p1 → p4) → (p4 → p3)) ∨ (p1 ∧ (p2 ∧ (p2 → p1))))) ∨ (False → ((p4 → p2) → p4))) → p3) → p3)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∧ (((p1 → p4) → (p4 → p3)) ∨ (p1 ∧ (p2 ∧ (p2 → p1))))) ∨ (False → ((p4 → p2) → p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



