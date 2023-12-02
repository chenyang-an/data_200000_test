variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262165898704158750252519829828 : (True ∧ (((p1 ∧ (p3 ∧ (p3 ∧ ((p1 ∧ (p1 → (p4 ∧ (p5 ∧ (((p5 → (True ∨ True)) → p5) → (p2 ∨ False)))))) ∧ p4)))) ∨ p1) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668617703475824435066806355220 : (((((p5 ∧ (((True → (p3 ∨ ((p4 ∧ p1) → ((p3 ∨ False) → (p5 ∧ False))))) ∨ (p3 ∨ p4)) ∧ True)) ∧ p2) ∨ (p5 ∨ (True ∨ p3))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_186647283765487738191116957513 : (((((p1 ∧ (True ∨ p2)) ∨ p1) ∧ p4) ∧ ((p5 → p4) → p1)) → ((((p4 ∧ (p2 → False)) ∧ ((False ∨ False) ∨ p5)) ∨ (False ∨ p1)) ∨ p2)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39770076535500195675926088380 : (((True → ((p5 ∨ (p2 ∨ False)) ∧ (((((p2 → p2) ∧ p4) ∧ p4) → (True → (((p2 ∧ (p2 ∨ p1)) ∨ p2) ∨ False))) ∨ False))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234577111060683446575240444299 : ((p3 → (True ∨ p1)) → ((p3 ∧ True) → ((((p5 → ((True → (p4 ∨ p3)) → p1)) ∨ True) ∨ p4) ∨ ((p2 ∧ ((p1 → p1) → True)) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52527208017186422456322829670 : ((((((p1 → (p4 ∧ p2)) → ((p5 ∧ p1) ∧ p4)) ∧ (p4 ∧ p5)) ∨ p4) ∨ ((False ∨ (False ∧ ((p4 ∨ (p5 ∧ p2)) ∨ p5))) → False)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226204868099727865241964696785 : (((p2 ∨ p1) ∨ p2) ∨ (((p3 ∨ p4) ∧ (p3 ∧ (((True ∨ p3) ∧ ((p1 ∨ False) ∧ (p2 ∧ p5))) ∨ False))) ∨ (False ∨ (True ∨ (p3 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103070746186812478485704350005 : ((((((p2 ∧ True) ∧ p5) ∨ p1) ∨ ((((p1 ∨ False) ∨ ((False → p2) ∨ (p1 ∨ p3))) ∨ (True → (p1 ∧ p1))) ∨ p3)) ∨ True) ∧ (True ∨ p3)) := by
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
theorem thm_5_vars_321173050380221999094362938921 : (p4 ∨ (p3 ∨ (((p1 ∧ (True ∨ p1)) ∨ (((False ∧ ((True → False) ∨ (p4 ∧ (p3 → (p1 → p4))))) ∨ (p3 ∧ p3)) ∨ (False → True))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694541308360580455997993008700 : ((((p1 ∧ ((p4 → ((p3 → p4) ∧ p3)) → (p1 ∨ (True ∧ (p4 ∨ p1))))) ∨ (((False ∧ p3) ∨ ((p2 ∧ p2) ∧ False)) → (p1 → p1))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51947028988208618224560536302 : ((((((p2 ∧ (p1 ∧ p1)) ∧ p2) ∧ p1) ∨ (False → ((True ∨ (True → True)) ∨ p4))) ∨ (p4 ∨ ((False ∨ (p4 ∨ (p5 ∨ p5))) ∧ p2))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756675207476318924099766097631 : (((p1 ∧ ((p5 ∨ (p4 ∧ ((p3 ∧ ((p1 ∧ p1) ∧ True)) ∨ (False ∨ (True ∧ p1))))) ∨ ((((p4 → p4) ∨ p4) ∧ (p1 ∨ p3)) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111816028893796813824166636563 : ((((p1 ∨ (p3 → (((p5 ∧ p3) → False) ∧ (p4 → ((True ∨ False) ∧ ((True ∧ p5) ∨ (p3 ∨ p5))))))) → (p2 → p3)) ∨ False) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38413733505490834287634567513 : ((((((p5 ∧ ((p2 ∨ p4) → p3)) ∧ (p1 → True)) → (p2 ∨ (p4 → p5))) ∧ (((p3 → p1) ∨ False) ∨ (True ∧ (p4 ∨ p3)))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206391517027075500808373966657 : ((p3 ∨ ((p3 ∧ (p5 ∧ p1)) ∨ p5)) ∨ (((p5 ∧ p2) ∨ (((False ∧ p2) → False) ∨ ((p3 → True) ∨ p5))) ∨ (False ∧ ((True → p1) → p5)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801884102632456059543231608718 : (((p2 → ((False → True) ∧ (((((p4 ∧ p5) ∧ ((((p5 ∨ p4) ∧ p5) → (p3 → False)) → (True ∧ p3))) ∨ (p4 ∧ p5)) ∨ p2) ∨ p2))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326892800103121179024604003677 : (True → (((p2 ∨ (p2 ∨ ((True ∨ p3) ∧ (((p3 ∧ p1) ∧ p2) ∨ ((False ∧ True) → (((False → p5) ∧ p5) ∨ (True ∨ p1))))))) ∨ True) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593146392079304393804131173355 : (((((((p1 ∨ p5) ∨ ((p3 ∧ True) ∧ (True ∨ p5))) ∧ (((p2 → p5) ∨ (p5 ∨ (p1 ∨ p5))) → False)) ∨ ((False ∧ p3) ∧ p4)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_239163651495103398382303628291 : ((p2 ∨ True) ∧ (((p4 → (p3 → (((p2 ∧ True) → p1) → (p3 ∨ ((p3 ∨ (p2 ∨ True)) ∧ (p3 → p5)))))) → p5) ∨ ((p3 ∧ p4) → p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260690885616107881422611776228 : ((p3 → p3) → (p1 ∨ ((True → False) → (((p4 ∨ p5) → (p4 ∧ (p4 ∧ ((((p4 ∨ p5) ∨ (p5 ∧ (p3 ∧ p1))) → True) → False)))) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782398620588581833341565620784 : (((p3 ∨ (((((p2 → (p1 ∧ p4)) ∨ p2) → ((p3 → ((True ∨ p4) ∨ p2)) → (((False ∧ p3) ∧ (p5 ∧ p5)) ∨ p4))) → False) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51061813460605878964821186700 : (((True → (False ∧ ((((True → p1) ∧ (p1 → False)) ∧ p1) ∨ (p2 → ((p3 ∨ p4) ∧ False))))) ∧ (p2 ∨ (p4 → (p5 → (p4 ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245313255010139643090140668534 : ((p2 ∧ p2) ∨ (((p5 ∨ p4) → p3) → ((((p1 ∨ (p5 → p5)) → (((p5 ∨ False) → p5) ∨ (p1 → False))) → False) → (True ∧ (p2 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p1 ∨ (p5 → p5)) → (((p5 ∨ False) → p5) ∨ (p1 → False))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h13 := h2 h3
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328149669072400579184442653334 : (True → ((p5 ∨ (p1 ∧ (((((p4 ∧ (p2 → (True → p5))) ∨ p4) ∧ p2) → (True ∧ ((p3 ∨ p4) → True))) → p5))) ∨ ((p3 → p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319451125731127814275703823410 : (p4 ∨ (((((p1 → ((p4 → p1) ∧ (p5 ∧ p4))) ∧ p5) ∧ p3) → p1) ∨ (p1 ∨ (((((p3 ∧ (p3 → p2)) ∨ False) ∧ False) → True) ∨ p4)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114740009159917068589654435076 : (((((p4 ∨ p1) ∨ p4) → (False → ((p2 ∧ True) → ((p3 → (p4 ∨ p5)) ∨ p1)))) → ((((p1 ∧ p2) ∨ p4) ∧ p4) ∧ p3)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178315147621065080094671792951 : ((((p4 → (False ∧ ((p2 ∨ p1) ∧ (p2 ∧ p2)))) ∨ p2) ∨ (p5 → p5)) ∨ (((True → p2) ∨ p5) ∧ ((p4 ∨ (False ∨ p1)) → (p3 → p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299454022611723914876078429852 : (False ∨ ((p3 ∨ ((p3 → p3) → (((((p3 ∨ p3) ∨ p2) → (p4 → (p5 ∧ ((p5 → p5) ∨ (p5 ∨ (False → p2)))))) ∧ p5) ∨ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51074920953000174519939603366 : (((p3 → ((((p2 ∧ p4) ∨ (((p4 ∨ p3) ∧ p1) → (p1 ∧ False))) → p2) → (p1 ∨ p5))) ∧ ((((p3 → p5) ∨ p5) ∧ p5) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56102650028755334911729001291 : ((((p5 ∨ p5) ∧ (p2 ∧ p5)) ∨ ((True → p5) ∧ (p4 ∨ ((p3 ∧ p5) → (True → ((p2 → (True ∧ ((p4 ∧ p4) ∨ p1))) ∨ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340967832479572891465107848494 : (p2 → (((p2 ∨ False) ∧ ((((p3 → p4) → p1) ∨ ((((p1 ∨ (p1 ∧ p3)) ∨ p4) → (p3 ∨ ((p3 ∨ p3) ∧ p5))) ∨ p4)) ∨ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174416643743346412798876224955 : ((((p1 → (p4 → p4)) ∨ (p3 ∧ (False ∧ p5))) ∨ ((p5 ∧ p3) ∨ (False → True))) → ((p5 ∧ p1) → (((p4 → (False ∧ p3)) ∧ False) ∨ p5))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137067907734305682847513952674 : (((p3 → p5) → (((((p3 ∧ p5) → p3) ∨ (False → (True ∧ True))) → (p4 → p5)) ∨ (p4 ∧ ((False ∨ p2) ∨ p4)))) ∨ (True ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325088542912336013356296015902 : (p5 ∨ ((False → p3) → (((p2 ∧ (p4 ∨ ((p2 ∧ (p3 → (p4 ∧ p1))) ∧ ((((True → p1) ∧ p2) ∨ p5) ∨ p4)))) → (p2 → p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49043656890352115705251848934 : ((((False → (p4 ∨ (((p1 ∧ (((p2 ∧ p3) ∧ p2) → ((p3 → p1) ∧ False))) → True) ∨ (p3 → False)))) → False) ∨ ((True ∧ p4) → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249718788702242374541023298119 : ((p5 ∨ p5) ∨ ((p1 → ((((False → False) ∨ (p2 ∧ p3)) → ((p3 ∧ True) ∨ False)) ∨ (((p4 ∨ p1) → (False → (p5 → p4))) ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117302746877470347437079174815 : ((False ∧ (((True ∧ True) ∨ ((p1 → (((p5 → (p3 → ((p5 ∧ False) ∨ True))) ∨ p3) ∨ (p2 → p3))) ∧ p1)) → (p3 → False))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57197137773000983708686363922 : ((((p4 ∨ p1) ∨ p5) ∨ ((((((p5 ∨ ((p3 ∧ ((p1 ∧ True) ∧ p1)) → p1)) ∧ (p2 ∨ (False ∨ p1))) ∧ p5) → False) ∨ False) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165074503604470477703334831831 : (((p5 ∧ ((((p4 ∧ (p4 ∨ (p5 ∧ (True → True)))) ∧ (p1 → True)) ∨ p5) ∧ p5)) → False) ∨ (((True ∨ p1) ∨ p2) → (False → (p1 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594888302056439117292020073955 : ((((((p2 ∨ True) ∧ (False ∨ (p2 ∧ ((True → False) ∨ (False ∧ (p4 ∨ p2)))))) ∧ (p4 → (((p3 ∧ (p1 ∧ p2)) ∧ p2) ∧ p4))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112091399226416605045207887093 : ((((p1 → p4) ∨ ((((p2 → p4) → ((p4 → p1) → p4)) ∧ ((p2 ∧ (True ∧ p5)) ∧ p5)) ∧ (p2 ∧ (True ∨ p1)))) ∨ p4) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690425141039352858230737125711 : ((((((False ∧ ((((p2 → p2) → p4) → p4) → (p3 ∧ (p2 ∧ p2)))) ∨ p4) ∧ p5) → (p1 ∧ ((p2 ∨ (True ∧ (True → p1))) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161782257599145196124327766151 : ((p4 ∨ (p4 ∨ ((((False ∧ (False ∨ p4)) → (p2 → True)) ∧ ((p4 → (p5 ∧ p4)) ∨ True)) ∨ p4))) → (True → (False ∨ ((p2 ∧ p5) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
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
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173005175724944344418095390130 : ((p5 ∧ ((p5 ∨ p2) → (p2 ∧ (p1 ∨ (((p4 ∧ (False ∧ p5)) → True) ∨ p5))))) ∨ ((False ∨ ((p4 ∨ (p5 → p2)) ∨ (False → False))) ∨ p2)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1487618623873008300536813951 : (((p3 → (((((False ∧ ((p2 → p1) ∧ p3)) ∧ (((p5 ∨ p4) → p5) → p4)) ∨ p3) ∨ p4) ∨ (False → p5))) → p5) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49712200119922213252703934134 : (((True ∧ (((p5 ∨ ((True ∨ (((p2 → p1) → ((p2 ∧ (p2 → False)) → p3)) ∨ p2)) ∨ p5)) → False) → True)) → (p4 → (p5 → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252649655731262980385339861102 : ((p5 → p4) ∨ ((((False → (p1 → ((p2 ∨ p1) ∧ ((True ∧ (p4 → True)) ∨ p3)))) → p1) ∨ p5) ∨ ((False ∧ (p3 ∧ p1)) → (p4 ∨ False)))) := by
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
theorem thm_5_vars_310293144596285109415418481637 : (p2 ∨ (((p5 ∧ ((p1 ∨ p3) ∨ (p2 ∧ (p1 ∧ p4)))) ∨ False) ∨ (((p2 → p3) ∧ p3) → (True ∨ ((p1 → (True ∨ p5)) ∨ (False ∧ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47167413192966233023756850041 : ((((p2 ∨ (p1 ∨ (p4 ∨ (True → (((p2 ∧ False) → p3) → (True ∧ False)))))) ∧ (((True → True) → (False ∧ p5)) ∧ p5)) ∨ (p4 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111781789746864638046467866588 : (((((p1 → ((False ∧ (((False ∧ ((p2 ∨ (p1 → (p4 → False))) → p2)) → p2) ∨ p3)) → p3)) → p1) ∨ (p1 → False)) ∨ p2) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745730784344795760614223295812 : ((((True ∨ p5) → (True ∧ (((True ∨ p4) ∨ False) → (p2 ∨ ((p1 ∨ (p2 → ((((False ∧ p3) ∧ p5) → (p3 ∧ p4)) ∧ p5))) ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263103652818343583079882631309 : (True ∧ (((p3 ∧ (p5 → (p5 ∧ ((False ∧ p4) ∧ ((p2 ∧ False) ∧ (((p3 ∨ (p1 ∨ p4)) → p1) ∨ p3)))))) ∨ (True ∨ p5)) ∨ (True ∧ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319068711225707934489030391761 : (p4 ∨ ((p4 → ((p1 ∧ (p5 ∧ p3)) ∨ ((((((p2 → p4) ∧ p4) → False) → (False ∧ p2)) → p2) ∨ p4))) ∨ ((False ∨ True) ∧ (p4 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735637397712688956208365642581 : ((((p5 ∨ p1) ∧ ((p2 ∨ (((False → True) → ((p4 ∨ False) ∨ (False ∧ p2))) ∧ ((((p2 ∨ p2) → p4) → True) ∧ False))) ∧ (p4 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645638256938750119828092845641 : ((((p5 ∨ ((((True ∧ p4) → True) ∧ (p5 ∨ (p2 → ((p3 → (p5 ∧ (True ∨ (((p2 → p2) ∧ p5) ∧ False)))) ∧ False)))) → p2)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_570651975407006623043192951917 : (((p1 → ((p4 ∨ (True → (((p1 ∧ ((p4 ∧ (p1 ∧ p2)) ∨ p2)) ∨ (p3 ∧ ((p1 → (True ∨ p1)) → p2))) ∨ (p2 ∨ True)))) ∧ p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58432370651249241159704647512 : (((p2 ∨ p5) ∧ (p2 ∨ ((((((p3 ∨ True) ∨ ((True ∧ False) → (False → p2))) ∧ (False ∨ p3)) ∧ p4) → (p1 ∧ p2)) ∧ (p4 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167899569953841092896240758384 : ((((((p5 → False) ∨ p2) ∨ p1) ∧ (p4 ∧ p3)) ∧ ((p3 → (p4 ∧ p2)) ∧ (p3 → p2))) → (p2 ∨ (p2 ∨ (p4 ∧ ((p1 ∧ False) ∨ p1))))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h5.left
      let h9 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h3.left
      let h11 := h3.right
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h5.left
      let h16 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h3.left
      let h18 := h3.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h5.left
    let h21 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h3.left
    let h23 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h20
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115718557110118802947175737512 : ((((((True ∨ False) ∧ False) ∧ p4) → p3) → (p1 ∧ (p2 → (((p1 ∧ (p2 → p1)) → p3) ∧ ((p5 ∧ (True → p3)) → p3))))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117070526659563976791293121320 : (((True → p1) → (p2 ∧ (p5 ∨ ((p3 → ((False ∨ p2) ∧ (False ∧ ((((p1 ∨ (p1 ∧ p1)) → False) ∧ False) ∨ False)))) ∨ True)))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660740033604947443646621045133 : ((((((False → (p2 → (False → p3))) ∨ ((p4 ∧ ((False ∨ ((p4 → ((p1 ∧ True) ∨ p3)) ∨ p3)) ∧ p4)) ∧ p1)) → p4) → (False ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116292035545348230433013428840 : (((p4 ∨ (p4 ∨ p5)) ∨ ((p2 ∧ ((p5 → (((p2 ∨ p2) ∧ (True ∧ (False → p4))) → p4)) → (p4 ∧ False))) ∨ (p1 → p5))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134361791541876636402288645391 : (((p1 ∨ (((((p5 → True) ∨ (p4 → (p5 ∧ p5))) ∧ (((p2 ∧ p5) → p3) → p4)) ∨ (p4 → p2)) ∨ p1)) ∨ p4) ∨ (p4 → (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313185158043362111610654133947 : (p3 ∨ (((((p1 → True) ∧ (p1 → p4)) ∧ p2) ∨ ((True ∧ (((p1 ∧ (p4 → False)) ∨ ((False → p4) ∧ (False → p4))) ∧ True)) ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653748979406614021382088113162 : ((((((((True → False) → ((p2 ∧ (p1 ∨ p2)) ∨ (p2 ∧ (False ∨ (p3 → True))))) → (p4 ∨ p2)) → (p3 ∨ p4)) ∧ p4) ∨ (p1 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344152079578147605075255077148 : (p2 → (False ∨ (p5 ∨ (p4 → (((((p5 → (((p5 → True) ∧ (True ∧ p5)) ∨ p1)) ∨ ((p4 ∨ p5) ∨ True)) → p5) ∨ (True → p4)) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617916783482093019267648770332 : (((((p2 ∧ ((p4 ∨ p3) ∨ (False ∨ True))) → ((((False ∧ p2) ∨ p2) ∨ True) ∧ (((True ∨ p1) → (p2 → (p1 ∨ True))) ∨ p4))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_164609820864360565599725070905 : (((p1 ∧ (p5 ∧ (((p5 → ((p1 → (p3 → (p3 ∧ p4))) → p1)) → p1) → p4))) ∧ p5) ∨ ((False ∧ True) → (False ∧ ((p2 ∨ True) ∨ p2)))) := by
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
theorem thm_5_vars_189837419434514556789200546780 : ((False → (p1 ∨ (((p1 ∧ False) → True) → (p3 → False)))) ∧ (p1 ∨ ((p5 ∨ ((((p2 ∨ p1) ∨ p1) → (False ∧ (p3 → p2))) ∨ p3)) ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189013099439088349747008196681 : ((((False → True) → False) ∨ ((True ∨ (p2 → p2)) ∨ p2)) ∧ (p5 → (p1 ∨ (((p2 ∨ (p1 ∨ False)) ∨ p2) ∨ (p2 → (p5 ∨ (p4 ∨ p2))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49128816721755416011520334034 : (((((p5 ∨ p1) ∧ (((True → p1) ∧ p3) ∨ ((False ∨ p1) ∧ True))) ∨ (((p2 ∧ p5) ∨ (p1 ∨ p3)) ∨ p3)) ∨ ((False ∧ p1) → p1)) ∨ False) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184365783595544249729059171226 : (((p2 ∨ (True → (((False ∧ p5) ∨ (p1 ∧ False)) → True))) → p3) ∨ ((((p4 → (p1 → (((p4 → p5) ∨ p1) → p1))) ∨ p2) ∨ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599411059084969331577200668089 : (((((p5 ∧ p1) ∨ ((((p2 ∨ ((((((p5 → True) ∨ p2) ∨ p1) → True) ∧ p1) → p4)) ∧ p2) ∧ (True ∧ (p3 → p1))) ∨ p5)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260361029734099054213327376640 : ((p2 → p5) → ((p3 ∨ (p5 ∨ ((p4 → ((p5 ∨ p3) ∧ p3)) → (False ∨ (((False ∨ p5) ∧ p5) ∨ p2))))) ∨ (p4 → ((p1 ∨ True) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1938191338612537235447035364 : (((((p3 ∧ ((p3 → (False ∨ p1)) → (p5 ∨ False))) ∨ p2) ∨ (p1 ∨ ((True ∧ p4) → p2))) ∧ True) ∨ (p4 → ((True ∨ True) ∨ p2))) := by
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
theorem thm_5_vars_198364399644913283097363847583 : ((p3 ∧ ((((p3 ∨ False) ∨ p4) ∧ p3) ∧ p5)) ∨ (((p2 ∧ p4) → ((p4 ∧ p3) ∧ (p2 ∨ p2))) → ((True → (False → (p1 → True))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179397383531691949322093906109 : ((p3 ∨ ((p3 ∧ True) ∧ (((p2 ∨ p1) ∧ p5) ∨ ((p3 ∨ p4) → p1)))) ∨ ((False ∧ ((p1 ∧ p4) → (False ∧ p1))) → ((False ∧ p5) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219582783428906625352700403027 : ((True → (True ∧ (p5 → p3))) → ((p5 ∧ p2) ∨ (((p5 ∧ ((False ∨ (p5 ∨ (p4 ∨ (p5 ∨ p1)))) ∨ True)) ∨ ((p2 ∨ p1) ∨ p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303870777358802839341134968192 : (p1 ∨ ((((p5 ∧ (p5 → (((p3 ∧ (p2 ∨ p3)) → p1) ∧ p3))) → (True → ((False ∨ (p2 ∨ True)) ∨ True))) → (p5 ∨ (p3 ∨ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258356428476144209625110783912 : ((p5 ∨ False) → ((((True ∧ (p3 → (p3 ∧ p3))) → (((p5 ∧ p4) → (p1 ∧ (p2 ∨ p2))) ∨ p4)) ∧ True) ∨ (((p1 → p5) ∨ True) ∧ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146995560311526622176716787817 : (((((((p5 ∧ p2) ∨ (((p3 → p1) → p4) → p5)) ∨ ((False → p2) ∧ p4)) ∨ True) ∧ (p4 → True)) ∧ p2) ∨ ((p5 ∧ (p1 → p1)) → p5)) := by
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
theorem thm_5_vars_61160096765838470981703926720 : ((False ∧ ((p2 → (p5 ∨ (p4 ∧ p4))) → ((p1 → False) ∧ (p2 ∧ ((p3 ∧ (p3 ∧ ((p2 ∨ p4) ∧ (False ∧ False)))) → (p4 ∧ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703167622765018699669045384692 : (((((p4 → True) → (p2 ∧ ((False ∨ p2) ∧ (True → True)))) ∨ (((p2 → p4) ∧ p2) ∨ (p4 → (True ∨ ((p3 ∨ p3) → (p3 ∨ p1)))))) ∨ p3) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299241649031669926945939781113 : (False ∨ (((((((p4 ∨ p3) → p5) ∨ (p4 → p1)) ∨ p2) → ((True → ((p2 ∧ (False → p1)) ∨ False)) ∧ p5)) ∨ (True ∨ (p2 ∨ p4))) ∨ p5)) := by
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
theorem thm_5_vars_260798334943455594791001946432 : ((p3 → p5) → (((p5 → p3) ∨ p4) ∨ ((p1 → (p1 ∧ p4)) → (((p5 → True) ∨ p4) ∧ (p1 ∨ (p1 ∨ (False ∨ ((p4 → p4) ∨ p2)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114103434040798024774402303432 : (((p4 ∧ (((p1 ∨ p2) → (((False → ((False ∨ (True ∧ (p4 ∧ p3))) ∨ p4)) ∨ p1) → p4)) ∨ p4)) ∨ (True ∨ (p4 ∧ p4))) ∨ (p4 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118329787852306402034043993073 : ((p2 ∨ ((((p5 ∨ ((p4 ∧ (p5 ∨ p3)) ∧ p4)) ∧ True) ∨ ((p3 ∧ ((p2 ∧ (p5 → True)) ∧ (True → p2))) → False)) ∧ p4)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117060374377549604697023087109 : (((p5 ∨ p2) → (((((True → (p4 ∧ p4)) ∧ (p1 ∨ (False ∨ p1))) ∨ False) → (p2 ∧ ((True ∧ p5) → True))) ∨ (p2 ∧ p1))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151640521966011933795044182372 : ((((((((True ∧ (True → (True ∨ p4))) ∧ (False ∨ p5)) → p4) → True) → p5) ∨ p5) ∧ (p2 ∨ (True ∧ p2))) → (((False ∨ p3) ∧ True) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47238418511194509461252305967 : (((((((p5 ∧ p3) → True) ∨ p2) ∧ (p4 ∨ False)) → (p1 ∨ (((p3 → False) → p4) → (((p1 ∨ p1) ∧ p3) ∧ False)))) ∨ (True ∨ False)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148580139941601614904529400375 : (((((True ∨ p2) ∧ ((True ∨ p4) ∧ (p5 ∧ p1))) ∨ p2) ∨ ((p1 → (p1 ∨ ((p5 → p2) ∨ p5))) → p5)) ∨ (True ∧ ((p1 ∧ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300826749607684987917080896828 : (False ∨ ((p4 ∧ (p2 ∨ (((True → False) → ((p5 ∧ (p5 → (p2 ∧ p1))) ∨ False)) → True))) → (p1 ∨ (p3 → (p4 → (p3 ∨ (p4 ∨ p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150289871720269868402062926831 : ((p4 → ((((True ∨ ((True ∨ (p1 ∨ (p4 ∨ p5))) → (p1 ∧ p5))) → p1) → (p3 ∧ (p3 ∨ p1))) → p2)) ∨ ((False ∧ p2) → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164810342883504550531331242231 : ((((True ∨ True) ∧ (((False → False) ∧ ((p2 ∨ (p1 ∧ (p1 ∨ False))) ∨ p5)) ∨ True)) ∨ False) ∨ ((True ∨ (True → (p1 ∧ (p5 ∧ p2)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674760431110000085840131333275 : ((((p3 → (False ∨ (((p3 → (p5 → (True → ((False ∧ p2) ∨ ((p1 ∧ p5) → p1))))) ∨ p1) → (p4 ∨ p5)))) → ((p5 → p2) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693437776955588131862028275201 : ((((p4 → (p5 → (((False → (p1 ∨ (True ∧ p2))) ∨ (p2 ∨ False)) ∧ p1))) ∧ (((p3 ∨ (False ∨ p4)) → False) → (True → (False ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50182437909771476140897571165 : (((((((p4 ∧ (p2 ∧ (p4 ∨ p3))) ∧ (p3 → False)) ∨ False) ∨ ((p4 → False) ∨ (p4 ∧ p2))) ∧ True) ∨ (True → (False → (False → p4)))) ∨ p1) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705886266584522193097606274127 : ((((((True → p5) ∧ p1) ∨ (p5 → (False ∧ p5))) ∧ ((p3 ∨ p1) ∧ (((((True ∧ False) ∧ p1) → (p4 → p2)) → (p1 → False)) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114477394247390453626410056871 : (((((p5 ∧ (True ∨ (((p2 ∧ p4) ∧ (True ∧ p2)) ∨ p1))) → (p1 ∨ True)) ∧ (p3 → p5)) → ((p3 ∨ p1) ∨ (p2 ∧ True))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62319966482486094394250765359 : ((p3 ∧ ((p2 → ((False ∨ (((p5 → True) ∧ (p4 ∨ (False ∨ p3))) ∧ (((p3 ∧ True) ∧ p4) ∧ (p3 ∨ p4)))) ∧ p2)) ∨ (p2 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



