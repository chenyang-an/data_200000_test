variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649351469580342523418154419808 : (((((True → (p4 ∨ ((p5 → ((p4 ∨ p5) → (p4 ∧ True))) ∨ (((p3 ∨ True) ∨ p2) ∨ (True ∧ (p2 ∨ p3)))))) → p4) ∧ (p5 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319450432892581700439927862581 : (p4 ∨ (((p5 ∧ ((p3 ∨ (p3 → False)) ∧ ((p2 ∧ p2) ∨ False))) ∨ True) ∨ ((((p1 → p5) → p5) ∨ (p3 → (p2 ∨ (p5 ∧ p4)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324311398244895493472937544088 : (p5 ∨ ((False → (True → (((p4 → p4) ∧ p4) ∨ p5))) → ((((p3 ∨ p4) ∨ p1) → p3) ∨ (((p1 ∧ p4) ∨ (p5 → (True ∨ True))) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163071645020876752938920491104 : ((((p4 ∧ (p5 ∧ p4)) → (((True ∨ p4) ∨ (p3 ∨ p3)) → p1)) → (False ∨ (p3 → True))) ∧ ((((p3 ∧ p4) ∨ p5) ∨ (p2 ∨ False)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_390962542572641917192768275242 : (((((((p3 ∨ p1) ∨ (p5 → p4)) → p2) ∧ ((((p1 ∨ p5) → (p4 ∧ ((p2 ∧ p3) ∧ ((p5 ∨ p5) ∧ p1)))) ∨ p3) ∧ p2)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_230526695353048106299791156275 : (((False → False) ∧ True) → ((p5 ∨ (p1 ∨ (True ∨ ((p5 ∧ (p5 ∧ p5)) ∧ p4)))) ∧ ((((p3 ∧ (p2 → p2)) → p1) → p4) ∨ (True ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247460391848740857194337851009 : ((False ∨ p2) ∨ (p5 → ((p5 → ((((p4 ∨ False) ∧ (p4 ∧ p4)) ∨ p4) ∨ (p2 ∨ (p5 ∧ ((p1 ∧ p1) → p4))))) ∨ (True ∨ (p2 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178480903819646396076839193765 : ((((True → ((p4 ∨ p1) ∧ (p4 ∨ True))) → p1) ∨ ((False ∨ p2) ∧ False)) ∨ (p2 ∨ (p5 → (True ∧ ((p5 ∨ (False → (p1 → True))) ∨ False))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252680759232840592099394672703 : ((p5 → p4) ∨ (p2 → (((p1 ∧ (p5 ∧ (p4 ∧ ((p1 ∧ (True → p1)) ∧ p3)))) ∧ ((p5 ∨ p5) → p3)) ∨ ((p1 ∧ (p5 ∨ False)) ∨ True)))) := by
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
theorem thm_5_vars_306217472949111036207421658992 : (p1 ∨ (((True ∧ True) ∨ p4) → ((p3 ∧ (True ∨ ((p1 ∧ ((False ∧ p4) → ((False ∧ p5) ∧ False))) ∨ True))) → (((p1 ∨ p5) ∧ p5) ∨ True)))) := by
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
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
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
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40739835872159602783321242158 : (((((p1 ∨ (False ∧ False)) ∧ ((p3 ∧ (True → p2)) → (((p3 ∨ True) → (True → (p5 ∧ p4))) ∧ ((p5 ∧ False) ∧ p4)))) → False) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114014045888295375611574005259 : ((((((p2 ∧ p3) ∨ ((((p5 → p5) → p3) ∨ (p1 → ((False → p2) → p2))) ∨ p5)) ∧ p4) ∨ p5) ∨ (p1 → (p1 → True))) ∨ (p1 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166642364725734459917801467398 : ((p1 → ((p2 → ((False → (((p3 → p2) → ((p4 ∨ p1) ∧ p3)) → p2)) ∧ p5)) → p5)) ∨ ((p3 → ((p2 ∧ p2) ∨ p2)) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608343866207788843716519548109 : (((((((False ∧ p5) ∨ (p2 ∧ (p2 ∨ ((((((p1 ∧ False) ∨ (p5 ∧ (False ∧ p3))) ∧ p3) ∧ p3) → p1) ∨ p1)))) ∨ p2) ∨ p5) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339481035770547691941554768939 : (p1 → (False ∨ (((p4 ∧ (p1 ∧ (p2 ∨ (True ∨ (((p2 ∧ p4) ∨ ((p1 ∧ (False ∧ ((p4 → p3) → p5))) ∨ p2)) → p1))))) → p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53272456035360317145629117907 : (((p1 ∧ (((p2 ∧ (p4 ∧ False)) → (p1 ∧ (True → p4))) ∨ p4)) ∨ (p2 ∨ ((p3 ∧ p4) ∧ ((p4 ∨ p2) ∧ ((p3 → False) ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111839876468567012173033906266 : (((((p4 → False) ∧ (p2 ∧ ((((True ∨ (True ∨ p3)) → (p4 ∧ p5)) → (True → True)) → False))) ∨ (p1 → (p5 → p2))) ∨ p3) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57595073391488764632378908471 : ((((False → p4) ∧ True) → (((p3 ∨ p1) ∨ False) ∧ ((False ∨ (p1 ∨ ((p5 ∧ True) ∧ (p2 ∧ p1)))) → (((p2 ∨ p1) → p3) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180663751241220338006998904164 : (((((p3 ∨ (p5 ∧ True)) ∨ p3) ∧ p4) → (p5 ∧ (p4 → (p2 → p3)))) → ((((p1 → p2) ∧ (p1 → (p3 ∨ p2))) ∧ (p4 ∨ True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624359624494454967245487402749 : ((((p3 ∨ (((True → p4) ∨ p1) ∨ (True → ((p2 → (p5 ∧ (False → p3))) → (((((p2 ∨ p4) ∧ p3) ∧ p5) ∨ False) ∧ True))))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788913235928185326121781459471 : (((p5 ∨ ((((p1 ∨ ((((p4 ∧ True) → (False ∧ p3)) → p2) ∨ ((p2 ∨ (False → p4)) → (False ∨ p3)))) ∨ False) ∧ p3) ∨ (True ∨ p5))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_305396331359395650894654665606 : (p1 ∨ ((((((((p4 ∧ False) ∧ p2) ∨ p3) ∨ p5) ∨ p2) → (p5 ∧ (p1 ∨ p3))) ∨ True) ∨ ((p3 ∨ (False → (p1 ∨ p1))) → (p5 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39283208316526155366737502556 : (((p1 ∧ ((((p3 ∨ p5) ∧ (True ∨ p1)) ∧ ((((p1 ∧ p2) → p3) ∨ p2) ∨ (p2 ∧ ((p5 ∧ (p1 → p1)) ∨ p2)))) → p1)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52267049400079539956950632196 : (((p5 ∨ (p5 → ((p5 ∨ (p4 ∧ True)) → (p4 → (((p1 → p2) ∧ p5) ∧ p5))))) → ((p2 ∨ (True ∨ (p2 ∧ (p4 ∨ False)))) ∨ p1)) ∨ p2) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313349778473301533949749195788 : (p3 ∨ ((p1 → (((((((p4 → p4) → p2) → False) → p5) ∨ p4) → (p2 ∧ (p3 ∧ True))) ∨ (True → ((p3 ∧ False) → (p4 ∨ p2))))) ∨ p5)) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661269155617434464709619754289 : (((((p3 → (p5 ∨ ((p5 ∨ ((True ∧ (p3 → (p3 ∨ (p1 → (p4 ∨ False))))) ∧ (p1 ∨ p2))) ∧ p4))) ∨ (True ∨ False)) → (p4 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68691350937011766020012973558 : ((p4 → (((True → (False ∨ ((False → True) → ((p2 ∨ False) → (p2 ∧ p5))))) → (p5 ∨ (((p1 ∧ False) ∨ p3) ∨ p4))) ∨ (p4 ∨ p5))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2093034761441325949725822474 : (((p1 ∨ p4) → ((p3 → ((p4 ∧ ((((p2 → True) → p2) ∧ False) ∨ p1)) ∨ p3)) ∨ False)) ∨ (p4 ∧ ((p1 → p1) ∧ (p1 → p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309635668204120874540427075486 : (p2 ∨ ((((p4 ∧ False) ∨ (True ∧ False)) ∨ (((False → p5) ∨ True) ∧ ((p1 ∧ p4) ∨ ((p3 → (True → p3)) ∨ p1)))) ∨ ((p1 → p5) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112256034475440421667368614245 : (((p4 ∨ (((p1 ∧ p3) ∨ (p3 ∨ p3)) ∧ (((True ∨ p5) ∨ (((False ∧ p1) ∨ (p5 → True)) ∨ True)) ∨ (p4 → p2)))) ∨ False) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609962825002994618890815075863 : (((((p5 → ((p1 ∨ (p1 → p4)) ∨ (((p5 → ((p3 ∨ p2) ∨ ((p3 ∨ p1) ∨ (p4 → (p2 ∨ p2))))) ∨ p4) ∨ p4))) ∨ True) ∨ p3) ∨ False) ∧ True) := by
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
theorem thm_5_vars_174394408767342136737024636107 : (((True ∨ (True → ((True → p1) ∨ (p1 → True)))) ∧ (p1 ∧ (p4 → (False → p2)))) → ((((((p3 ∨ p2) ∨ p1) ∧ p3) ∧ p5) ∨ p1) ∨ p5)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789070706868955569101507423239 : (((p5 ∨ ((((p1 ∧ ((((p3 → (((True ∨ p3) → p4) ∨ p3)) → (p4 ∨ p3)) ∨ p2) ∧ True)) ∧ p2) ∨ p5) ∧ (p1 ∧ (p5 ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148256927016616133625880399159 : (((p2 ∧ (((p4 ∧ True) ∨ (p2 ∨ ((True → p5) ∧ ((True ∧ p2) ∧ True)))) ∧ True)) ∨ (p1 ∧ (p5 ∨ p4))) ∨ (((p2 → p2) → False) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68830265084299239085001137232 : ((p4 → ((p1 → (False ∧ p3)) → ((False ∨ ((p5 ∧ True) ∨ ((p4 → (p2 ∨ (False ∨ (p5 ∨ p5)))) ∧ p4))) ∨ ((p4 → p2) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42986477188799625709762098170 : (((p5 → (True ∧ ((((((p3 ∨ ((p2 → p3) ∨ p2)) ∧ ((p2 ∨ p5) ∨ p4)) ∨ p4) ∧ p3) ∧ ((p5 → p2) ∨ p1)) ∨ p5))) ∨ p1) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170015137335428764402757045043 : ((((p4 ∧ (p3 → (p2 ∨ ((p3 → p4) ∧ p5)))) ∨ p3) ∨ ((True → p1) → True)) ∧ ((True → False) → ((((p4 ∨ p2) ∨ p1) → p1) ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_110856340184780936144357334994 : (((((p2 ∨ ((((p2 ∧ False) ∧ p1) ∨ ((True ∧ (p1 → ((p3 ∧ p3) ∨ (p5 → False)))) → p5)) ∨ p4)) ∧ p1) → p2) ∧ p3) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191140806010905811867531253865 : ((((p1 ∧ True) ∨ p4) ∨ (((False ∧ p5) → p3) ∧ p4)) ∨ (((((p5 ∧ True) ∧ (((False ∨ (p4 ∨ False)) → p5) ∧ False)) → p3) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112031757342947160980986813887 : (((((p2 ∧ p1) → p4) ∨ ((p3 ∧ ((False ∧ (False ∧ ((p2 ∧ (p3 → (p5 → (p5 → p3)))) ∨ False))) ∨ p2)) ∧ p4)) ∨ True) ∨ (p5 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309305897722775678071355841707 : (p2 ∨ (((p1 → (False ∧ ((((p5 ∨ p4) ∧ ((((p4 → p3) → p3) → p5) ∧ p4)) ∧ ((p2 ∧ True) ∨ False)) ∧ p1))) ∧ p5) ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180566280380649182028738654127 : (((((p1 ∨ (p4 → (p5 ∨ p4))) → p2) → True) → ((p2 ∧ p5) ∧ p3)) → ((True ∨ (p4 ∨ ((p4 ∨ True) ∧ (True ∧ True)))) → (p5 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (((p1 ∨ (p4 → (p5 ∨ p4))) → p2) → True) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h4
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h11 : (((p1 ∨ (p4 → (p5 ∨ p4))) → p2) → True) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h13 := h1 h11
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h18.left
        let h21 := h18.right
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h22 : (((p1 ∨ (p4 → (p5 ∨ p4))) → p2) → True) := by
          -- Implications on the right can always be decomposed.
          intro h23
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h24 := h1 h22
        -- We need to get the left conjuct of h24 based on <expert-advice>.
        let h25 := h24.left
        -- We need to get the right conjuct of h25 based on <expert-advice>.
        let h26 := h25.right
        -- One of the premise coincides with the conclusion.
        exact h26
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h18.left
        let h29 := h18.right
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h30 : (((p1 ∨ (p4 → (p5 ∨ p4))) → p2) → True) := by
          -- Implications on the right can always be decomposed.
          intro h31
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h32 := h1 h30
        -- We need to get the left conjuct of h32 based on <expert-advice>.
        let h33 := h32.left
        -- We need to get the right conjuct of h33 based on <expert-advice>.
        let h34 := h33.right
        -- One of the premise coincides with the conclusion.
        exact h34
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h35 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h36 : (((p1 ∨ (p4 → (p5 ∨ p4))) → p2) → True) := by
      -- Implications on the right can always be decomposed.
      intro h37
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h38 := h1 h36
    -- We need to get the left conjuct of h38 based on <expert-advice>.
    let h39 := h38.left
    -- We need to get the right conjuct of h39 based on <expert-advice>.
    let h40 := h39.right
    -- One of the premise coincides with the conclusion.
    exact h40
  case inr h41 =>
    -- Disjunctions on the left can always be decomposed.
    cases h41
    case inl h42 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h43 : (((p1 ∨ (p4 → (p5 ∨ p4))) → p2) → True) := by
        -- Implications on the right can always be decomposed.
        intro h44
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h45 := h1 h43
      -- We need to get the left conjuct of h45 based on <expert-advice>.
      let h46 := h45.left
      -- We need to get the right conjuct of h46 based on <expert-advice>.
      let h47 := h46.right
      -- One of the premise coincides with the conclusion.
      exact h47
    case inr h48 =>
      -- Conjunctions on the left can always be decomposed.
      let h49 := h48.left
      let h50 := h48.right
      -- Disjunctions on the left can always be decomposed.
      cases h49
      case inl h51 =>
        -- Conjunctions on the left can always be decomposed.
        let h52 := h50.left
        let h53 := h50.right
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h54 : (((p1 ∨ (p4 → (p5 ∨ p4))) → p2) → True) := by
          -- Implications on the right can always be decomposed.
          intro h55
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h56 := h1 h54
        -- We need to get the left conjuct of h56 based on <expert-advice>.
        let h57 := h56.left
        -- We need to get the right conjuct of h57 based on <expert-advice>.
        let h58 := h57.right
        -- One of the premise coincides with the conclusion.
        exact h58
      case inr h59 =>
        -- Conjunctions on the left can always be decomposed.
        let h60 := h50.left
        let h61 := h50.right
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h62 : (((p1 ∨ (p4 → (p5 ∨ p4))) → p2) → True) := by
          -- Implications on the right can always be decomposed.
          intro h63
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h64 := h1 h62
        -- We need to get the left conjuct of h64 based on <expert-advice>.
        let h65 := h64.left
        -- We need to get the right conjuct of h65 based on <expert-advice>.
        let h66 := h65.right
        -- One of the premise coincides with the conclusion.
        exact h66



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718666969978549117032383989154 : (((((p3 ∨ p4) ∧ (True → False)) ∨ (p5 ∨ ((((p1 ∨ (True ∨ False)) ∨ ((p2 → (True ∧ (True ∧ True))) ∧ (p1 ∧ p3))) ∨ p3) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111876342075921187323066241403 : (((((p2 ∨ (((False → (True → p4)) ∨ (((p5 ∧ p3) → p1) ∧ p4)) ∨ p4)) ∨ p2) → (((p5 ∧ p5) → p2) ∧ p1)) ∨ True) ∨ (p5 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725736986306692860813998543901 : (((((p1 ∨ p4) ∧ p4) ∨ (((True → False) ∧ ((p3 ∧ False) → ((False ∧ False) → (p3 ∨ p2)))) ∨ (True → (((False → p2) ∨ p2) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43749505263047176842297108543 : ((((True ∧ ((p3 → p4) → ((p5 ∧ ((p4 ∨ p2) ∨ p3)) ∧ (p2 ∧ ((p5 ∨ True) ∨ ((False ∧ p4) ∨ (p2 ∨ p2))))))) → p5) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138430666896292441513069578617 : ((p5 → (((((p3 ∨ p3) → False) → (((False → p5) → p2) ∧ (p2 → p5))) ∨ False) ∧ (p5 ∨ (True ∨ (p5 ∨ False))))) ∨ ((p3 → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2471578115636318332508754138 : ((p1 ∨ (((p2 → p1) ∧ ((p2 ∨ p2) ∨ p3)) ∨ p5)) ∨ (False → (False ∧ (p3 ∨ (((p5 ∧ p5) ∧ p2) ∨ (False ∧ (p5 ∨ p3))))))) := by
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
theorem thm_5_vars_732284446398139939981086711637 : ((((False ∧ False) ∧ (((((p1 ∧ ((p2 ∧ (p2 ∨ p3)) ∧ (True ∨ (p1 ∧ (True ∧ False))))) ∨ (p2 ∧ p1)) ∧ p2) ∧ (p2 ∨ p4)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637106762438133140868659245994 : (((((((p2 ∨ True) → ((p2 ∧ ((True → True) ∧ p2)) ∧ False)) → p3) ∨ (((((p3 → (True ∧ True)) → False) ∧ False) → False) → p3)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98803908452124929505989684613 : ((True → ((((((p2 ∨ True) ∧ True) ∨ (p3 ∨ (((p2 → p4) ∨ (p3 → (p4 → False))) ∨ (p2 ∧ False)))) ∧ p3) ∧ (p4 ∧ p3)) ∧ False)) → p3) := by
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
theorem thm_5_vars_328831941357559743055720159284 : (True → ((p2 ∧ (p1 → (((p3 ∨ (False ∧ p4)) ∧ True) ∧ p1))) → (((p5 → p3) ∨ (p4 ∨ p2)) ∨ (((p5 → False) ∧ (p5 ∨ p5)) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160198294061975586128811062977 : (((p5 → ((((p4 ∧ p2) → p4) ∧ (p3 → ((p2 → (True ∨ p2)) → False))) ∧ p2)) ∧ (False → p1)) → (False ∨ (p5 → ((True → p3) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807397682924104603452160781098 : (((p4 → (((((p3 ∨ (False ∨ p3)) ∨ (p2 ∨ p4)) → p2) → p4) → ((True ∧ (p1 → ((p5 → p5) → p3))) ∨ (False → (p5 ∧ p1))))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118382355770500287241775194545 : ((p2 ∨ (((True → (p3 ∨ False)) → ((p5 ∨ (False ∨ p3)) ∨ True)) ∧ ((((p1 ∧ p1) → p2) → p5) ∨ (p3 → (False ∧ p4))))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114167011393523648721080447192 : ((((p1 ∨ ((True ∨ ((p2 ∧ (p2 → p3)) ∧ (False → (False ∧ p4)))) → ((p3 ∨ p2) ∨ p4))) → p4) → ((p2 → p5) ∧ p4)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693538932028508564076956265948 : ((((((p5 ∧ (p1 ∧ p1)) ∧ (p1 → ((False ∨ False) ∨ (p5 → p1)))) ∧ p2) ∨ ((p1 ∧ ((p5 ∨ (True ∨ (p4 ∧ p1))) ∧ p3)) → p3)) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200045181840465391416886190389 : (((p1 ∨ (p3 → (False ∧ p2))) → (p1 ∧ p4)) → ((((True ∨ p5) ∨ p4) → p3) ∨ ((True → p2) ∨ ((((True ∧ p5) ∨ p2) ∧ p2) → True)))) := by
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
theorem thm_5_vars_252451117620930452567802707139 : ((p5 → p1) ∨ ((p1 ∨ (True ∧ ((p4 ∧ (p5 ∨ p5)) → ((((p1 → ((p2 ∨ p3) → (False ∧ (p3 ∧ p5)))) ∨ False) ∨ p4) ∨ p3)))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784385327070726901246783761005 : (((p3 ∨ (p3 ∧ (((p4 ∧ p1) → ((p2 ∨ False) → p1)) → ((True ∧ (p4 → p5)) ∨ ((False ∨ True) ∨ (True ∧ (p1 → (False ∧ p5)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675223939841824782109973094795 : ((((((p5 ∧ p5) → ((((True ∧ p2) ∨ p3) ∧ ((True → p3) ∧ (p2 ∧ False))) ∧ (p4 ∨ p3))) ∨ True) ∧ (False → ((p3 ∨ True) ∧ False))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301967488305475008522210189824 : (False ∨ ((True → p2) → (p4 ∨ ((True ∨ (((((p5 → ((p1 → (False ∧ p1)) ∧ (p2 ∧ p1))) → p4) ∨ p5) ∨ p4) ∨ (p2 → p1))) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h10 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h11 := h1 h10
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h12 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h13 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h14 := h1 h13
          -- One of the premise coincides with the conclusion.
          exact h14
      case inr h15 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h17 := h1 h16
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h18 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h20 := h1 h19
      -- One of the premise coincides with the conclusion.
      exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249289109880266348362151192136 : ((p4 ∨ p5) ∨ ((((p3 ∨ ((p4 → (p4 → False)) → (p2 ∧ (p2 ∧ ((p4 ∨ (p4 → (p1 → False))) ∧ True))))) → (p1 ∧ True)) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226596908482273093274629294783 : (((p5 → p1) ∨ False) ∨ ((((p3 ∧ (p2 ∨ (p4 ∧ p4))) ∧ (True → (p4 → True))) ∧ (True → False)) → ((p1 → p3) ∧ (False ∧ (p4 ∨ p5))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h13.left
  let h16 := h13.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h15.left
  let h18 := h15.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h19 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h20 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h21 := h14 h20
    -- False on the left can always be used.
    apply False.elim h21
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h25 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h26 := h14 h25
    -- False on the left can always be used.
    apply False.elim h26
  -- Conjunctions on the left can always be decomposed.
  let h27 := h1.left
  let h28 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h29 := h27.left
  let h30 := h27.right
  -- Conjunctions on the left can always be decomposed.
  let h31 := h29.left
  let h32 := h29.right
  -- Disjunctions on the left can always be decomposed.
  cases h32
  case inl h33 =>
    -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
    have h34 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h28, we can now drive its conclusion.
    let h35 := h28 h34
    -- False on the left can always be used.
    apply False.elim h35
  case inr h36 =>
    -- Conjunctions on the left can always be decomposed.
    let h37 := h36.left
    let h38 := h36.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780197818126645212159939462802 : (((p2 ∨ ((((p5 → (((False ∨ (p4 → True)) → p3) ∨ ((p4 → p5) ∨ (p2 → p4)))) → p1) → (p1 → p3)) ∨ (p3 → (p3 ∧ True)))) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586505818519984812075888044329 : (((((((p3 → False) → p1) → (p2 ∨ (p4 → (((p3 ∨ (p5 ∨ ((((False → True) → p3) ∧ p3) → False))) ∨ False) → p3)))) ∧ True) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47593493446279738839430661938 : (((p3 → (((p3 ∧ (((p5 ∨ ((True ∧ ((False → p2) ∧ (p4 ∧ p3))) ∨ p4)) ∨ p2) ∨ (p4 ∧ p4))) ∨ False) ∧ False)) ∨ (True → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54006532157328456806239246607 : (((((p5 ∨ ((p4 → p2) ∧ True)) ∧ (p4 ∨ False)) → p5) → ((p1 ∨ ((p2 ∨ ((p1 → (p2 ∧ p2)) ∧ True)) ∧ p2)) ∨ (False → p3))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172223093622537378894564262942 : (((p5 ∨ (((p2 → ((False → p5) ∧ p2)) ∨ p1) ∨ False)) → ((p5 ∧ p3) ∧ False)) ∨ ((((p2 ∧ p4) ∧ (p2 ∧ (p2 ∧ p4))) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225182962107235180046255161639 : (((p4 ∧ p1) ∧ p4) ∨ ((((p1 ∧ p5) ∨ ((p4 → ((p4 ∧ p1) ∨ p5)) → (p2 ∧ p2))) ∨ (True ∨ (False → (p4 ∧ p3)))) ∧ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164828265718111192051961455075 : (((True ∧ ((((((True ∧ p3) ∧ p3) ∧ (p2 ∧ True)) ∨ p2) ∨ (p1 → p1)) ∧ p2)) ∨ p4) ∨ (True → (False ∨ ((p2 ∧ (p5 ∧ True)) → p5)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136359019456384974736793537798 : (((((p3 ∨ p2) → True) ∧ p1) ∨ ((p4 → (((p2 ∨ p1) → p2) ∨ ((((p3 → True) → p1) → p1) ∧ p2))) → p4)) ∨ ((p2 ∨ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215998213169769228808368689944 : ((p4 ∨ (p5 ∨ (p5 ∧ p1))) ∨ (p2 ∨ (p1 ∨ ((((True ∧ ((True ∧ p1) ∨ p4)) ∨ ((True ∧ (p2 ∧ p4)) → p1)) ∨ (True ∨ p4)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_264204852526491586266128665468 : (True ∧ ((p1 ∧ ((False ∧ (False ∧ False)) ∨ (False ∨ p3))) → (((p4 ∧ p3) ∧ ((p4 ∨ p2) ∨ ((p4 ∧ p5) → (p2 ∧ (p1 → False))))) ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219062714054782650901795236016 : ((p5 ∧ (p5 ∧ (True → True))) → (((p3 → p1) ∨ p1) → ((p2 ∨ True) → (((p4 ∨ p1) ∨ p5) → (p3 → (((p4 ∧ p2) ∨ p3) ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h1.left
          let h11 := h1.right
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h1.left
          let h16 := h1.right
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h1.left
          let h22 := h1.right
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h23
        case inr h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h1.left
          let h27 := h1.right
          -- Conjunctions on the left can always be decomposed.
          let h28 := h27.left
          let h29 := h27.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h28
    case inr h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h32 =>
          -- Conjunctions on the left can always be decomposed.
          let h33 := h1.left
          let h34 := h1.right
          -- Conjunctions on the left can always be decomposed.
          let h35 := h34.left
          let h36 := h34.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h35
        case inr h37 =>
          -- Conjunctions on the left can always be decomposed.
          let h38 := h1.left
          let h39 := h1.right
          -- Conjunctions on the left can always be decomposed.
          let h40 := h39.left
          let h41 := h39.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h40
      case inr h42 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h43 =>
          -- Conjunctions on the left can always be decomposed.
          let h44 := h1.left
          let h45 := h1.right
          -- Conjunctions on the left can always be decomposed.
          let h46 := h45.left
          let h47 := h45.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h46
        case inr h48 =>
          -- Conjunctions on the left can always be decomposed.
          let h49 := h1.left
          let h50 := h1.right
          -- Conjunctions on the left can always be decomposed.
          let h51 := h50.left
          let h52 := h50.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h51
  case inr h53 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h54 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h55 =>
        -- Conjunctions on the left can always be decomposed.
        let h56 := h1.left
        let h57 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h58 := h57.left
        let h59 := h57.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h58
      case inr h60 =>
        -- Conjunctions on the left can always be decomposed.
        let h61 := h1.left
        let h62 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h63 := h62.left
        let h64 := h62.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h63
    case inr h65 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h66 =>
        -- Conjunctions on the left can always be decomposed.
        let h67 := h1.left
        let h68 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h69 := h68.left
        let h70 := h68.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h69
      case inr h71 =>
        -- Conjunctions on the left can always be decomposed.
        let h72 := h1.left
        let h73 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h74 := h73.left
        let h75 := h73.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h74



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190142775724772095173347574242 : ((((False ∨ p3) ∨ (((p5 ∨ p2) ∧ p4) ∧ p1)) ∧ p4) ∨ ((((p5 ∨ ((p2 ∨ p5) → p3)) → True) ∧ (p3 ∧ ((False ∨ p3) → p2))) → p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198045020603174990079410591323 : (((p2 ∧ p4) ∨ (p5 → (p5 → (p2 ∧ p2)))) ∨ (False ∨ (False ∨ ((((p4 ∨ ((p4 ∨ False) ∨ False)) ∧ p2) → False) → (p5 ∨ (p3 → True)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64798728103359726068233557518 : ((p2 ∨ (((p5 → False) → ((((False ∧ (((p5 ∨ (((p4 ∨ False) ∧ (p5 ∨ False)) ∨ False)) ∧ True) ∨ p2)) → False) ∨ True) → p3)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726174263219255944272516885646 : (((((p4 ∧ p4) ∨ p4) ∨ ((False ∨ True) ∧ (p5 ∨ (((p5 ∨ True) ∨ p4) → ((p5 ∨ (p4 → (p1 → ((p5 ∨ p1) → p4)))) ∨ p4))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h5
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190700195641880210299398934486 : (((((p2 ∨ True) ∧ (p5 ∧ p5)) ∨ p1) ∧ (p3 ∧ p2)) ∨ ((p4 ∧ (p3 ∧ (((((p3 → (False ∨ p4)) → p2) ∧ p2) → p1) ∨ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611849061086981740344539014756 : (((((p3 → (p3 → ((p5 ∧ ((((p1 → p1) ∨ True) → ((p4 ∨ (p2 ∧ p2)) → p1)) → (p5 → False))) → (False ∨ False)))) → p2) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47951852212968392934116924409 : (((((((((p1 ∧ p4) ∧ p5) → p5) → (p2 → (p2 ∧ (True ∨ p3)))) → True) ∧ (p1 ∧ p5)) → ((False ∧ p2) ∧ p1)) → (p5 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124203154238528179017942356431 : (((p2 ∨ (p2 → ((False → (p1 ∧ (p3 → p2))) ∨ p4))) ∨ (True ∧ ((p3 ∧ p1) ∧ (p1 → ((True ∨ (p2 ∧ p4)) → p5))))) → (p1 → p1)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310441554511477670532414338987 : (p2 ∨ ((True → ((p1 ∨ False) ∧ (True → (False ∨ p2)))) → ((p2 ∧ False) ∨ (((((p2 ∨ p3) ∧ p3) ∧ False) ∨ p5) ∨ ((True → p4) ∨ True))))) := by
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
theorem thm_5_vars_159532596529538521810247495316 : (((p1 ∧ (((p2 ∧ (p5 ∨ (p1 ∨ (((True ∧ False) ∨ False) ∨ p2)))) ∨ (p3 → p3)) → p1)) ∧ p4) → ((False ∧ (False ∧ (p2 → False))) ∨ p1)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173941661442232390127529164070 : (((((((p5 ∨ p3) → (p1 ∨ False)) ∨ p3) ∨ p2) ∨ ((p4 ∧ False) ∨ p2)) → p1) → ((p1 → p5) ∨ (True → (((p1 ∨ True) ∨ p4) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54182362073511548553205091780 : ((((p4 ∧ ((p1 ∨ (True ∧ p2)) → p4)) ∧ True) ∧ (((p1 ∨ p1) → p1) → ((p1 → (p4 ∧ p4)) ∨ ((p4 ∧ p4) ∨ (p3 ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313277770721035751371961661084 : (p3 ∨ ((p2 ∧ ((p1 ∧ p4) ∧ ((p4 ∨ (False → (((p4 ∨ (p1 ∨ (True ∨ p2))) ∧ (((p5 ∨ True) ∨ p4) ∧ p5)) ∧ True))) ∧ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80339798156782134601847155064 : ((((p4 → (((False ∧ False) ∧ p1) ∨ (p5 ∨ (((p3 ∧ (False ∧ p4)) ∨ p1) → p1)))) ∨ ((p4 ∧ (p4 → True)) ∨ p4)) → (True ∧ False)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 → (((False ∧ False) ∧ p1) ∨ (p5 ∨ (((p3 ∧ (False ∧ p4)) ∨ p1) → p1)))) ∨ ((p4 ∧ (p4 → True)) ∨ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186933967671884805736922816088 : (((p3 ∨ (p1 → p5)) ∧ (((p1 → p2) ∧ p1) ∧ (False ∨ p4))) → (False ∨ (p4 ∧ (p5 ∨ ((False → p2) ∧ (p5 → ((p5 ∧ p2) ∧ p4))))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h12
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h13 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h14 := h7 h13
      -- One of the premise coincides with the conclusion.
      exact h14
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h3.left
    let h17 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h20 =>
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h21
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h22 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h23 := h15 h22
      -- One of the premise coincides with the conclusion.
      exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638795217960801227678459375919 : (((((p4 → ((p4 → p2) ∨ (p5 ∨ p3))) → (((True → (((p4 ∨ p1) ∨ (True ∧ False)) → p4)) ∧ ((p2 → p2) ∨ p1)) ∨ p5)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193152910805395598566853810915 : (((p1 ∨ ((p2 → p1) ∨ p3)) ∨ ((True ∨ False) ∨ p3)) → (p5 → (((False → p1) → p2) → (((p3 ∨ p1) ∨ (p5 ∨ True)) ∨ (p1 ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137688538289431239503559133372 : ((p1 ∨ (((((((True → False) ∨ (((p5 ∨ (p2 ∧ p2)) ∧ p2) → (True ∧ p5))) ∨ p4) ∧ p2) ∨ p5) ∧ p2) → p1)) ∨ ((True ∧ p5) → p5)) := by
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
theorem thm_5_vars_172506819515875935427982391811 : ((((p2 ∧ p5) ∨ p5) ∧ ((((p1 ∨ p5) ∨ p4) ∧ (True ∨ (p4 ∧ p5))) ∧ p4)) ∨ (((p2 ∨ True) → (False ∧ ((True ∧ p1) ∧ p5))) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135084989344164670181756559418 : (((((p4 ∧ p4) ∧ (p4 ∨ ((((p2 ∨ p5) ∨ p4) ∨ p4) ∧ True))) ∧ ((p2 → (p3 → p4)) → p2)) ∨ (p4 ∧ True)) ∨ ((False → True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299138681306186934623669492688 : (False ∨ ((((p1 ∨ ((p3 → (True → ((((p4 → p3) → False) → False) ∧ p2))) ∨ p5)) → (p2 → (True → ((p3 ∨ p4) ∨ p2)))) ∨ False) ∨ p5)) := by
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
      exact h2
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171197375694196326055280059949 : ((p2 → (p1 ∨ ((p3 ∨ (p4 ∧ p1)) ∨ (((p2 ∧ p4) ∧ p4) → (True ∨ p4))))) ∧ ((p3 ∨ ((p5 ∧ (False → (True ∧ p5))) ∨ True)) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358641381078998565228762285447 : (p5 → (p4 → ((((((False ∧ p4) ∨ (True ∨ p5)) → (((((p3 ∨ p1) ∨ p5) ∨ False) ∧ p5) ∧ (p5 ∧ p1))) ∨ p1) ∧ (False → p2)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136827568313151928807312553136 : (((False ∧ p1) ∨ ((p4 ∨ (p1 → ((p3 → (((p1 → False) → (p4 → (True ∨ p4))) → p5)) ∨ True))) → (p2 → p3))) ∨ (p4 → (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337346204075554970580503391911 : (p1 → (((((p4 → True) → p4) → (p1 → (((((p5 ∧ p2) ∨ p1) ∧ (p1 → p5)) ∨ (p4 → p3)) ∧ p3))) ∨ p2) ∨ ((p4 ∨ True) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



