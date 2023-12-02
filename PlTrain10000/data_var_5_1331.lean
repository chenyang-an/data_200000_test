variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58834755444343526579451534592 : (((True ∧ False) ∨ (((True → (False ∨ ((p5 ∨ (False ∨ (p5 ∨ (True → True)))) → (p3 ∨ p1)))) ∧ p2) ∨ (True ∨ ((p4 → p5) ∨ False)))) ∨ p3) := by
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
theorem thm_5_vars_65443853046777530801647371823 : ((p3 ∨ ((p4 ∧ True) ∨ (p5 → (p4 ∧ (((False ∧ p3) → p5) → ((p1 ∧ (p2 → p3)) ∧ (((True → (p5 ∧ p4)) → p3) ∨ p2))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328928335249765335267435854632 : (True → ((p3 ∧ (((True ∧ (p4 ∨ p3)) ∨ False) ∧ True)) → ((((False ∧ ((p3 ∨ False) ∧ (p5 ∧ p1))) ∧ ((p3 ∨ True) → p4)) ∨ True) ∨ p1))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
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
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601165515214859369351771926879 : ((((p2 ∧ (((((((p4 ∧ p4) → (p2 → (True → (p3 → p1)))) ∨ p4) → p4) → (False ∧ True)) ∨ (p5 ∨ (p2 ∧ p2))) ∧ p1)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_392180227086199119442625286774 : ((((((True → p2) ∨ p4) ∧ ((((p3 ∨ ((p2 ∨ True) ∨ p5)) → p4) ∨ (True ∨ (False ∨ ((p4 → p4) ∧ True)))) → (p4 ∨ p4))) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300413841371348420986801279685 : (False ∨ ((p1 → ((p1 → ((p4 → (p3 → (p5 ∨ p4))) ∧ False)) ∨ (True → (((p4 ∨ p4) ∨ (p2 ∨ False)) → False)))) ∨ ((False ∧ True) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_148784186338486457636159600116 : (((True ∧ ((p3 ∧ (p3 → p3)) ∧ p4)) ∨ (p1 → (((p4 → True) → (p5 ∨ False)) ∨ (p2 ∨ (False ∨ True))))) ∨ ((p4 ∨ p3) → (True → False))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233109006634273063034843487191 : ((p4 ∧ (p4 → p1)) → (((((p4 ∧ p2) → ((((p3 → (((p5 ∨ p5) ∨ p5) ∨ p3)) ∧ p2) ∧ p5) ∧ (False ∨ p5))) → p5) → p5) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231106242553846383318271003180 : (((False ∨ p5) ∨ True) → (p2 → (((((((False ∨ p5) ∨ p2) ∧ (((False ∧ False) ∧ (p1 ∧ True)) → p3)) ∧ False) ∨ p1) ∧ True) ∨ (p3 → True)))) := by
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
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
theorem thm_5_vars_734842527929587786505431608652 : ((((p2 ∨ p2) ∧ (((p1 ∧ ((p1 ∧ (p5 ∧ ((((((p2 → p2) ∧ p1) ∧ (True → p1)) ∨ p2) → p2) ∧ p2))) → False)) ∨ p3) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669987690536280213014802480491 : (((((p3 ∧ (p1 ∨ ((p3 ∧ p1) → (p2 ∧ (p3 → p3))))) → ((False ∨ (p3 ∧ p2)) ∧ (False → (True ∨ p2)))) ∨ ((False → p1) ∨ p1)) ∨ p2) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319554096760049450166820617453 : (p4 ∨ ((True ∧ ((p3 ∧ ((p3 ∧ (p3 ∨ False)) ∨ p4)) ∧ p4)) ∨ ((((p1 ∧ (p4 ∨ p4)) ∨ (((p3 ∨ True) ∧ False) ∧ p4)) ∧ p3) → p4))) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662624926279427747381236526399 : (((((((p4 → p4) ∨ p1) → False) ∧ (((p2 ∧ ((p2 → (p2 ∨ (p1 ∧ p3))) → ((p5 ∧ p2) → p3))) → p2) ∧ p1)) → (p2 ∧ False)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : ((p4 → p4) ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h12 : ((p4 → p4) ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h13 := h8 h12
  -- False on the left can always be used.
  apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784334796938106549476882681945 : (((p3 ∨ (p2 ∧ ((p2 → (((p2 ∨ (p3 ∧ p1)) → p4) ∧ (((p2 → ((p3 ∨ False) ∧ (True ∧ p4))) ∧ (True → p5)) → p2))) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764141827478956272920842366266 : (((p3 ∧ (p4 → ((((p5 ∧ ((True ∧ (p2 ∧ False)) ∨ p2)) ∧ p5) ∨ (p1 ∧ True)) ∧ (p5 ∧ (((p2 ∧ p4) ∨ (True → p4)) ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197230637985255462586330774673 : ((((((p3 ∧ p2) ∧ p1) ∧ p5) → p1) → p3) ∨ (p3 → (((True → ((((p2 ∧ p3) ∨ p3) ∧ (p2 → p3)) → True)) → (p3 ∨ p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698423105057869556185538261894 : (((((((True → (False → False)) → p5) → False) ∧ (p1 ∧ (False ∧ p3))) ∨ (p5 ∧ ((p1 → ((p2 ∧ p4) → p1)) → (False ∧ (p5 → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40715669814339874344007313957 : (((((p4 ∨ ((p4 → p3) ∨ (p2 → (p5 ∨ p5)))) ∧ ((False → ((p2 → (p5 → (True ∨ (p1 ∨ p5)))) ∧ p1)) ∨ p2)) → p4) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65566302493043145324230310116 : ((p3 ∨ (p3 → ((((((p5 → True) ∧ p1) → (True ∧ ((True ∧ p1) ∧ ((p3 ∨ p3) ∧ p2)))) ∧ (p1 ∨ p1)) ∨ p3) → (p2 → p2)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747073953189585368206937957635 : ((((p4 ∨ p4) → (p1 ∨ (p5 ∨ (((p2 ∧ ((True → (p5 ∨ True)) ∧ ((p2 ∨ p1) ∧ (p1 → False)))) ∧ False) ∧ ((False ∧ True) → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190758621338096882247056896846 : (((p2 → ((False → p4) → (p5 ∧ p3))) ∧ (p5 ∨ p1)) ∨ (((p2 → (p3 → True)) ∨ (((False ∨ (p1 ∨ (True ∨ p2))) ∧ p3) ∧ p5)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616137983738468718713564149058 : ((((((p2 ∧ ((p4 → (p5 ∨ (p5 ∨ False))) ∨ p2)) ∧ (p2 → p3)) ∧ (True ∨ (False ∨ (False → (p4 ∨ ((False → p5) → False)))))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305790570599517234358911278416 : (p1 ∨ ((((False ∨ ((p4 ∨ p1) ∨ False)) → p3) ∧ p3) → (((p1 → (((p4 → p3) ∧ (True ∧ True)) → p4)) ∨ p3) ∨ (p3 ∨ (p2 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319404735271894933139922460996 : (p4 ∨ (((False → False) ∧ ((((p3 ∨ False) → p4) ∧ (p5 ∨ (p1 ∨ p2))) → p2)) → (((p4 ∨ ((p2 → p4) ∨ p4)) ∨ True) ∨ (True ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160199951295081130333569188877 : (((((p4 ∨ (False ∨ (False → (p5 ∨ (False ∧ ((True → p1) ∨ True)))))) ∧ p5) ∧ p3) ∨ (True → p5)) → (p1 ∨ (((True ∧ p3) → False) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135440249834524666877692115423 : (((p5 → ((False ∧ p2) ∨ (((p1 → ((p1 ∨ p4) ∧ (p4 → (p4 ∨ False)))) → p2) ∨ p2))) ∨ ((p1 → True) ∨ p1)) ∨ ((p5 ∨ p5) ∧ True)) := by
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
theorem thm_5_vars_196924239501562772319498506226 : (((((p2 ∨ p4) → (p5 ∨ p1)) ∧ True) ∨ p4) ∨ ((((p4 → p1) → (p2 ∧ ((p1 ∧ p1) ∧ ((p4 ∨ False) ∧ p4)))) → (p1 ∧ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225418091936400390162164944245 : (((p3 ∨ p1) ∧ p2) ∨ (p5 → ((False → p1) ∧ (((p2 → (p1 ∧ (False ∧ p3))) → ((p2 ∨ (p3 ∨ True)) ∨ (p2 ∧ False))) ∨ (p1 ∨ p1))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114886867776141327322045438329 : (((p2 ∧ ((p5 ∧ (p2 → ((False → p4) ∧ True))) ∨ ((p5 ∧ p1) → p2))) ∨ ((False ∨ p2) ∨ ((False ∨ p1) → (True ∨ True)))) ∨ (p5 ∧ p4)) := by
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
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67975288250913476348528174184 : ((p2 → (((True → p5) ∧ p2) → (((p4 ∨ p3) ∧ ((True → False) ∨ p5)) ∧ ((((False ∨ p2) → True) ∧ p5) ∧ ((p3 → p3) ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54754161955098053721826277263 : ((((p4 ∧ p4) ∨ ((p2 → (p1 → p4)) ∨ p3)) → (((False ∨ (((p5 ∧ p2) ∨ (False ∨ (p2 → p1))) ∨ (p3 ∧ p4))) ∧ p4) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54850819391727413539341113215 : ((((((False → p2) ∨ p4) ∨ False) ∧ p2) ∧ ((((p2 ∧ (False → p3)) ∨ p1) ∧ ((p4 ∨ ((False ∧ False) ∨ False)) → p2)) → (p2 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166015805835217907650054089547 : (((p3 ∨ False) ∨ (p2 ∧ (p5 ∧ (((p4 ∨ p1) ∧ p2) ∨ (p2 → (p2 → (True ∧ p5))))))) ∨ ((False ∧ False) → (((p4 ∧ p5) ∨ True) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55601032867589226035641849968 : (((True → ((p1 ∧ True) ∧ (p4 ∧ p4))) → (((p4 ∧ False) → ((True ∧ ((p3 ∧ (p3 ∨ False)) ∧ p4)) → (False ∧ False))) → (p5 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722853491704023945508987975399 : (((((p1 ∧ p3) ∨ p5) ∧ (((p4 ∨ p2) ∨ ((((((p1 → True) ∧ p3) ∧ (p1 ∧ p5)) ∧ p5) ∨ (False ∧ (p3 ∨ p5))) → p3)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337698756744488325405692261254 : (p1 → (((((p1 ∨ (((p2 → p1) → p2) → p3)) ∧ p5) ∨ (True ∨ False)) → (False ∨ (p4 ∧ p5))) → (((p1 → p1) ∧ (p3 ∨ p5)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p1 ∨ (((p2 → p1) → p2) → p3)) ∧ p5) ∨ (True ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690156198285235235205488722060 : ((((p2 ∨ ((((p5 ∨ (p4 ∨ p5)) → ((p5 ∧ (p5 ∧ p2)) ∨ p3)) → p3) ∨ True)) ∨ (p3 → (p1 → (p2 ∨ (p5 → (p4 ∨ p1)))))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47098604915595497959758524848 : ((((((p3 ∨ p3) ∧ (p3 ∨ ((((p2 ∨ False) → (p5 ∧ False)) → (False ∨ True)) ∧ p3))) ∨ True) ∧ (p4 ∨ (p2 ∧ p5))) ∨ (p1 → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655355638877897295829186185567 : (((((((((((p5 ∧ p3) ∨ p5) → (True ∧ p4)) ∧ p2) ∧ p2) ∨ (p5 ∨ ((p1 ∨ p1) ∧ True))) ∨ True) ∨ (p4 ∨ p4)) ∨ (p1 → p4)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_123912391884416982270043582719 : ((((((p1 ∧ False) ∧ (((p1 ∧ p5) ∧ p2) ∧ False)) → p3) → False) ∧ (p4 → ((p2 ∨ ((p4 ∧ (p1 → False)) → False)) → p5))) → (p5 ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p1 ∧ False) ∧ (((p1 ∧ p5) ∧ p2) ∧ False)) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h4
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652678662336180659421861103632 : ((((p1 ∨ (((False → (p2 ∨ False)) → (p1 ∧ p4)) → (p5 ∨ (p3 ∨ (p3 ∨ ((((p3 → p4) ∧ p5) ∧ p4) ∧ p4)))))) ∧ (p2 → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621451595827301806346305743980 : ((((False ∧ (((p3 ∨ p2) ∧ (p2 → ((((p5 → p4) ∨ False) ∧ ((p4 ∨ (p1 → p3)) → False)) ∨ (True → (p1 ∧ p1))))) ∧ p5)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621098293591783524728925397425 : (((((p3 → p3) → ((p5 ∧ (p2 → ((((p1 → ((p2 ∧ p1) ∨ p2)) ∧ p1) ∨ (True ∧ p3)) ∧ p2))) ∨ ((False → p4) → False))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147307625201914335518857152040 : (((((p5 ∨ (p3 → (True ∧ True))) ∨ (((p4 ∨ (p5 ∨ True)) → ((p4 ∧ p3) → False)) ∧ p4)) → p1) ∨ p4) ∨ ((True ∨ (p3 ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115574907253392559399350454629 : ((((True → ((False → p1) → p4)) → False) ∧ ((p2 → (p3 ∧ p2)) ∨ (((p1 ∧ False) ∧ p1) ∧ ((p3 ∨ p1) ∧ (p5 ∨ p2))))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157988772998884851341077437947 : ((((True ∨ (True ∨ (p5 ∧ True))) ∧ (False → p2)) → (p3 ∨ (p5 ∨ (True → (p5 ∧ (p2 ∨ p5)))))) ∨ ((False ∨ (p2 → True)) ∨ (p4 → p2))) := by
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
theorem thm_5_vars_676585032892997362575036690710 : ((((p2 ∧ ((((((p4 ∧ p2) → (False ∧ (False ∨ p4))) → False) → p2) ∨ (False ∨ (p5 ∧ p3))) ∧ p2)) ∧ ((p4 ∧ (p1 ∨ p5)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117864394401775631603853933395 : ((p5 ∧ (((((p4 → ((False → p1) ∧ (True ∨ p1))) → p5) ∧ (((False ∧ False) ∧ (p3 ∨ False)) ∧ (True ∧ True))) ∨ False) ∨ p2)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10516611632677382167881041145 : (((p2 → (p3 → (((False ∨ True) ∧ (((p3 ∧ False) ∨ (p5 ∨ p4)) ∨ (p1 ∧ ((True ∧ (False → p5)) ∧ p3)))) ∨ (p5 ∨ p2)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218319006512653745881123315460 : (((True → p2) ∨ (p5 ∧ p3)) → ((False ∨ p5) → ((((p4 → ((p5 ∧ p1) ∧ (p3 ∨ p4))) → p4) ∨ (True → p3)) → (p1 → (p3 ∨ p1))))) := by
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
    cases h2
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117680177276688756319395432266 : ((p3 ∧ (((((p4 → True) → p4) → p1) ∨ p3) ∨ ((((False → ((p2 → False) ∨ (p5 ∨ p3))) → (p2 ∨ p5)) ∨ p1) ∧ p3))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135846426018602410507379450077 : (((p4 ∨ ((True → (True ∨ True)) ∧ (p1 ∨ (True ∨ (p5 ∨ p4))))) ∧ (((p2 → (p5 → (p1 ∨ p4))) ∨ p1) ∨ p1)) ∨ ((p1 ∧ p4) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122798684954577787279691961859 : ((((((p5 → (((False ∨ ((p2 ∧ (True → (True ∨ p1))) ∧ p1)) → p4) ∨ p2)) ∨ p2) ∨ p5) ∧ p2) ∧ ((p5 ∧ True) → p5)) → (p4 ∨ p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63413936027649150391706100689 : ((p5 ∧ (p5 ∨ ((((p5 → p2) → p4) ∨ p1) ∧ (False → (p4 → (((p1 → p3) → p1) ∧ ((p1 → p3) ∧ (p4 ∨ (p2 → p1))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64583078189595813935177918457 : ((p1 ∨ ((p5 ∧ True) ∧ (((True ∨ True) → (p2 → ((False → True) → (((((p1 ∧ p3) → False) → p2) ∨ p3) → (p2 ∧ p1))))) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803061208431266243001183080888 : (((p3 → ((((p4 ∨ p2) → True) → ((False ∧ True) ∧ ((((p4 ∨ (p3 ∧ (True ∧ p2))) → p5) ∧ (p4 ∨ p4)) ∧ (True ∨ p4)))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193322364556315987937154090417 : (((p2 → (p3 ∧ False)) ∨ (p3 ∨ ((p2 → p2) → p2))) → ((p4 → (True ∧ (False ∨ (p5 ∨ (p5 → p4))))) ∨ (p2 → ((p2 ∨ p4) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
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
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137767768879333129266843762565 : ((p2 ∨ (((p5 ∧ ((p4 ∨ p1) ∨ p4)) ∨ ((p2 → True) → (((p5 ∧ p1) → p4) ∧ False))) ∨ ((p4 ∧ p4) → False))) ∨ ((False → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113806355502179714357237224633 : (((True ∧ ((((p5 ∧ p1) → True) ∧ p4) → ((p1 → (((True → p1) ∨ (p2 ∨ True)) ∧ (p2 ∨ p1))) → True))) → (p5 → p1)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50390292651475070119096738296 : ((((p5 ∨ p5) ∨ (p4 → ((False ∨ ((False ∨ False) ∧ (True → p5))) ∧ ((p4 ∧ True) ∨ (p1 ∧ False))))) ∨ (((p5 ∨ p1) ∧ False) → p5)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_184862854086211861191907417576 : ((((p3 ∨ p1) ∨ p2) ∧ (p2 ∨ ((p3 ∧ (False ∨ p4)) → p1))) ∨ (((p1 → ((p2 → p5) ∧ (((True → p2) ∨ p1) → p2))) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114914453869011272516489760031 : (((((p1 → p2) ∧ (((p2 ∧ (p4 ∧ False)) ∧ (False → p5)) → p1)) ∨ p2) → ((False ∧ p2) ∨ (p3 ∨ (p1 ∨ (p2 ∨ p4))))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61511147226051414106262355343 : ((p1 ∧ ((((p3 ∧ p5) → ((p5 ∨ p1) ∧ (False ∨ False))) → (((p4 → p5) → p4) ∧ (False ∨ False))) → (((p5 → p2) → p2) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691059772384894505670607038145 : (((((p3 ∨ (((p3 ∨ (p2 ∨ p4)) → (p4 → p1)) ∧ p2)) ∨ ((p3 → True) ∧ p5)) → ((((p4 ∧ p5) ∨ (False ∧ False)) → True) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52304865732720740741039017237 : ((((p2 ∧ ((False ∨ ((((p2 ∨ p2) ∧ p1) ∨ p2) → False)) ∨ True)) ∧ p4) ∧ (p4 → ((((True → p2) ∧ p3) → (p2 ∨ True)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134080100875821944560510119991 : ((((((p3 → (True ∧ p4)) ∨ (p1 ∨ ((False → p1) ∧ p5))) ∧ ((p5 ∧ (p5 ∧ True)) ∨ (p4 → False))) → False) ∨ p2) ∨ (True ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703279545663504318494114789800 : ((((p3 ∧ (p1 ∨ ((((p3 → True) ∨ p4) ∧ True) → p3))) ∨ ((False ∧ ((p2 → True) ∨ ((p4 ∧ (True ∨ p4)) → False))) → (p3 ∨ False))) ∨ p5) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177690773436818149046521820989 : (((((p1 ∨ (p3 ∨ p3)) ∧ (False ∨ (p2 ∨ False))) ∧ (p1 → p1)) ∧ False) ∨ (((p4 → True) ∨ (((p3 ∨ p1) → p2) → (p4 → False))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608155866726241473576769089005 : ((((((((p4 ∧ p1) ∧ p2) → (((p2 ∨ ((p2 ∨ ((False ∧ (False → p3)) → p5)) ∨ (p2 ∨ True))) ∨ False) → False)) ∧ p5) ∨ True) ∨ p1) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_1980168927161838763894977958 : ((p1 → ((True ∧ p5) ∧ ((((((True ∧ True) ∧ p2) → p4) → ((p2 ∧ False) → True)) ∨ True) → p2))) ∨ ((True ∨ (True ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593945347747565907251321651579 : ((((((((False ∧ True) ∨ p4) → p2) ∨ (p1 ∨ ((True ∨ (p4 ∧ p2)) → ((p1 ∧ True) ∨ p4)))) ∨ (False → (True → (True ∨ False)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217523369272934766140066624811 : ((((False → p4) ∧ p5) → p3) → ((((p3 → True) → ((((False ∧ p5) ∨ p5) → False) → (p3 → True))) → (False ∨ p5)) ∨ (p1 ∨ (p3 ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115622753134344036951085919132 : (((p4 → ((p1 ∧ False) ∨ (True ∨ True))) ∧ (((p4 → ((p5 → p5) → (((p5 → p4) ∨ p3) → (True → p1)))) → p3) ∨ p4)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115820275325134306486878639105 : ((((False ∧ p3) ∨ (p4 ∧ True)) ∧ (((((p4 ∨ p1) ∧ p1) → p2) → p2) ∨ (p5 → (p2 → (((False → p3) → p2) ∨ p4))))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328439119732713350616524592939 : (True → (((((p3 ∨ p3) ∧ (False → p2)) ∨ (((p2 ∧ p4) ∧ ((p4 ∧ True) ∧ p5)) ∧ p4)) ∧ True) → ((p1 ∨ ((p4 ∨ False) → p3)) ∨ True))) := by
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
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
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
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h14.left
    let h18 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160115330217538036090360987196 : (((p3 → (True ∧ (p2 ∨ ((p1 ∨ p3) ∨ ((p4 → (True ∨ False)) ∨ ((p3 ∧ p3) → p5)))))) → False) → (((False → True) ∧ p1) ∨ (p5 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → (True ∧ (p2 ∨ ((p1 ∨ p3) ∨ ((p4 → (True ∨ False)) ∨ ((p3 ∧ p3) → p5)))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
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
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148436292741024383813798060367 : (((True ∨ ((p4 → ((False ∨ p2) ∧ p3)) → ((False ∧ False) ∨ (p5 → p1)))) → (((False ∨ p5) ∨ p2) ∨ p2)) ∨ (False ∨ (False → (p3 → p1)))) := by
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
theorem thm_5_vars_171277223366589812411332249532 : ((p5 → ((p5 ∨ ((p4 ∧ False) → (p1 ∧ p1))) → ((True → (False ∨ False)) ∨ p5))) ∧ (p1 ∨ (p3 → (p4 → (p1 → (True → (True ∧ p3))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157812911306317820981602066333 : (((((p1 ∧ p3) ∧ ((((p1 ∧ p3) ∧ p3) → True) ∧ False)) → False) → ((p4 ∧ (p1 → p4)) ∨ p2)) ∨ (p5 → ((p2 ∧ (p4 → p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53196958192938246587369975248 : ((((((p4 ∧ p5) ∨ p1) ∧ (p2 → (p1 ∧ True))) ∨ (p4 → p2)) ∨ (((p5 ∧ (p2 → False)) ∨ p3) → (False → (p4 ∧ (p4 ∧ True))))) ∨ False) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3007889504247437070280446812 : (((False → False) ∨ p2) → (((False ∧ (False ∨ ((p5 ∨ True) → False))) → p2) ∧ ((p4 ∧ (p3 ∨ p4)) ∨ ((p1 ∨ (p2 ∧ p3)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316923132237182442232427282658 : (p3 ∨ (p2 → ((((True ∧ True) → p3) → ((False ∨ p5) ∨ ((((False → p4) → p1) ∧ False) ∨ (p1 → (p3 → (p3 ∨ p2)))))) ∧ (p3 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111247688337413588008868080575 : ((((True ∧ p1) ∨ (((((p2 ∧ ((p2 ∨ True) → (((True ∧ False) → True) ∧ (p4 → True)))) ∧ p1) ∨ True) ∧ p3) ∧ False)) ∧ True) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656274427778841350560351322346 : ((((((p2 ∨ (p4 ∨ p3)) → (False ∧ ((p5 ∨ p5) ∧ (p2 ∧ p3)))) ∧ (p4 ∨ ((False ∨ ((p3 → p5) ∧ p3)) ∨ p5))) ∨ (p2 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111177979449273169938524321606 : ((((p5 ∨ (p2 → (p4 ∨ False))) ∨ ((p1 ∨ (((p4 ∧ ((False → p3) ∨ p4)) ∧ False) ∨ (p4 ∨ False))) → (p4 ∧ p4))) ∧ p2) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115968773829385347286954665451 : (((((False → p3) → p1) ∧ p2) → (p5 ∨ (((False ∨ False) ∨ (p1 → p4)) ∧ (True ∨ ((p2 → ((p2 ∨ p3) → False)) → p4))))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248413059884539648401963295230 : ((p2 ∨ p4) ∨ ((p5 ∧ p5) ∨ ((p4 ∧ (False → p4)) ∨ (((p4 → p2) ∧ ((True ∨ True) ∧ False)) ∨ ((p3 ∧ ((p1 → p2) → p3)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_683932984544156971063763535681 : ((((((((p2 ∧ p2) ∧ ((p3 ∨ (p4 ∨ p4)) → p3)) → ((p1 ∧ p5) ∨ p2)) ∨ True) → p4) ∨ (((p1 ∨ (p4 ∨ p5)) → p4) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310201537440084006017118980479 : (p2 ∨ (((p2 ∨ (p4 ∨ ((p3 → (p1 → p3)) ∧ (True ∧ p3)))) ∧ p5) ∨ (p5 ∨ ((p3 → (True ∨ (p3 → (p3 ∨ (True ∨ p2))))) ∨ p1)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63274579567805217937386165062 : ((p5 ∧ (((p2 → False) ∧ (False ∨ False)) ∧ (p4 ∨ (((((p4 → (True ∧ (p4 ∨ (True ∧ True)))) → False) ∨ True) ∧ p1) ∧ (p2 → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223400285723949849194681977255 : ((True ∨ (True → p4)) ∧ ((((True ∧ p2) ∧ (p2 ∨ ((p4 → (True ∨ (((False → p3) → p1) → (p3 → p3)))) → (p4 → p5)))) ∨ p4) ∨ True)) := by
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
theorem thm_5_vars_207018193617241312983295549744 : ((((p1 → False) ∨ (p1 ∨ p5)) ∧ p2) → ((p3 ∨ ((True ∧ (p4 ∨ p2)) ∨ p4)) ∨ ((((True ∨ False) ∨ p3) ∧ True) ∧ ((p5 ∨ True) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
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
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661818308359695951041975201280 : (((((((p1 → False) → (((((True ∨ (p4 ∧ p1)) ∨ False) ∨ p5) ∧ p3) → p2)) ∧ p5) → (((p4 ∧ True) → p2) → p5)) → (False ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606743604665738517907962363695 : ((((((False ∧ ((p5 ∧ p1) ∧ (p4 ∧ (True ∨ (((True → (((True → p2) ∨ p5) ∧ True)) ∨ False) ∨ True))))) ∨ (True ∨ False)) ∧ p3) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_48011269048947155413009494303 : (((((p1 → (p4 → (((p1 → p1) ∧ (True ∧ p5)) → p1))) ∨ True) ∧ (p2 → (((True ∧ False) ∨ (p5 → p3)) ∨ p1))) → (True → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94519510563413273041217468252 : ((p2 ∧ (p2 → (((p3 ∨ ((p5 → p1) ∨ ((p4 → p4) ∧ (p4 ∧ p5)))) ∧ (((True ∧ (p5 ∧ (p1 ∧ False))) ∧ p3) → False)) ∧ p3))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49009564439085047251867191030 : ((((((p5 ∨ (p4 → (p5 ∧ p2))) ∨ ((p5 → p3) → ((p1 → ((False ∨ p2) ∧ p5)) → False))) ∨ p3) → p4) ∨ (True ∨ (p4 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786403481392466280272371329391 : (((p4 ∨ (((p1 ∨ (True ∨ p2)) ∨ (((((p1 ∨ False) ∨ False) → p3) ∨ p5) → False)) ∧ ((p4 ∧ True) ∧ ((True ∧ p3) → (p4 ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49089486427139993193059575257 : ((((p2 ∧ (((p4 ∧ ((p3 ∨ False) → ((p3 → (p5 → p4)) ∨ p5))) ∧ p1) → p3)) ∧ (p4 → (p4 ∧ True))) ∨ (p1 ∨ (p4 ∨ True))) ∨ p4) := by
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
theorem thm_5_vars_173424987949067404206637748544 : ((p5 → ((False ∨ True) → ((p2 ∨ ((p3 ∧ (False ∨ p2)) ∨ False)) ∨ (p2 ∨ True)))) ∨ (((p2 → ((p4 ∨ (p4 ∧ p3)) ∧ p4)) ∧ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



