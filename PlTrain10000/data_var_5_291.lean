variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37471340582969667577921701851 : (((((True → (True ∧ ((p5 ∨ p2) ∧ p4))) ∧ ((True → True) ∧ (((False ∨ (((False → p2) → p4) ∧ p1)) ∨ p5) ∧ p3))) ∨ p2) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309640811618411517068309040500 : (p2 ∨ (((p2 ∨ p3) ∧ ((p5 ∧ (p3 ∧ (p1 ∨ p1))) ∨ ((p5 ∧ (p4 ∧ ((p2 ∧ p5) ∧ False))) → (p1 ∨ True)))) ∨ ((p1 ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315507992074587795958366490408 : (p3 ∨ ((True → (p4 ∧ p1)) → ((((((p5 ∧ p3) → p3) ∧ (p2 → ((p1 → p4) ∨ p1))) → (p2 → False)) ∧ (False ∧ (p2 → p5))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138369282850879542836650177809 : ((p4 → ((((False ∨ (p5 ∧ p4)) ∨ (False ∧ (False ∨ p2))) ∨ p4) ∨ ((((False → p4) ∨ p5) → p3) ∨ (p3 ∧ True)))) ∨ (p4 ∧ (p4 ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618609237578767138387720963220 : (((((p2 → (p2 ∧ (p4 ∧ p4))) → ((p1 ∨ ((p3 ∨ (((p2 → (True → p2)) → p4) ∨ True)) ∨ (p4 ∧ (p2 ∨ p4)))) → p4)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190086786314001704203959941709 : (((((p5 → p2) → (p4 ∨ p2)) ∧ (p2 ∨ p5)) ∧ p3) ∨ (((((False → (True ∧ (True → p3))) → (p2 ∧ p4)) → p3) → (p3 → p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244600044230691889315811540808 : ((False ∧ p4) ∨ (p4 ∨ (p2 ∨ (((((p1 → (((True ∨ ((p1 ∨ (p5 ∧ p4)) → p3)) ∨ p3) → (p4 ∨ p1))) ∧ True) ∨ p5) ∨ True) ∨ p5)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729993462618883965660679736264 : (((((True ∨ p1) → p1) → (p1 ∧ ((((False ∨ (p5 ∧ True)) ∨ ((False → ((p4 → True) ∨ p5)) → False)) → (p4 ∧ (p5 ∨ True))) ∨ True))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p1) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315124358771338843267052272460 : (p3 ∨ (((p3 ∧ False) ∧ ((False ∨ p5) ∨ True)) ∨ ((p4 ∨ True) ∨ (False → (p4 ∧ (p4 ∧ ((False ∨ (True ∧ (True ∨ (True ∨ p5)))) ∨ True))))))) := by
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
theorem thm_5_vars_159206236455521348064695455913 : ((p2 → ((((p5 ∧ True) → (False → (p3 ∨ p1))) → (True ∧ p5)) → (p5 ∨ ((False ∨ False) ∧ p4)))) ∨ (p3 ∧ ((p5 ∧ (p3 ∨ p1)) ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p5 ∧ True) → (False → (p3 ∨ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h3
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606455516060283899569473788350 : ((((((p4 ∨ (p2 ∨ ((((((False ∨ p4) → False) → (p4 ∨ (p2 ∧ p2))) ∧ True) ∧ False) ∧ ((p2 ∨ p1) ∨ False)))) ∨ False) ∧ p3) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_328336730403969512815641941797 : (True → (((p1 ∧ (((p4 ∨ (p5 → p3)) ∨ (p3 → p2)) ∧ (p4 ∨ True))) → (False ∧ ((p1 → True) ∨ p3))) → (p3 → (p3 ∨ (p4 → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184774712918428494394456839355 : ((((False ∧ (p5 ∨ False)) ∧ p1) ∨ (p2 ∧ (False ∧ (p2 ∨ p5)))) ∨ (((False → p1) → p4) → ((True ∨ ((True ∧ True) ∧ True)) ∨ (p4 ∨ p5)))) := by
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
theorem thm_5_vars_919157821085818220601684579247 : ((((((True ∧ ((p1 → p3) ∧ (p2 ∨ p3))) ∨ p2) → (p2 → (p2 → p4))) ∧ ((((p3 ∧ False) ∨ ((False ∨ p3) ∨ p4)) → False) ∧ p4)) → False) ∧ True) := by
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
  have h6 : ((p3 ∧ False) ∨ ((False ∨ p3) ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68621674294639498375408183811 : ((p4 → (((False ∧ True) ∧ (((p1 ∧ (p5 ∧ True)) ∧ ((True ∨ (p4 ∧ ((((p4 ∨ True) ∧ p2) ∧ True) ∧ p5))) ∧ p3)) ∧ p1)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304678735604403279034977243469 : (p1 ∨ ((((((p3 ∨ p1) → p3) ∨ p1) ∨ (p5 ∧ (((p2 → False) ∧ (p4 ∧ ((p5 → p1) ∧ p5))) ∧ (p5 ∨ p1)))) ∧ p1) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138070253775866108174631748637 : ((True → (p3 → ((((p4 ∨ p5) ∧ p4) ∨ (((p1 → (((p3 ∧ p5) ∨ (p4 ∧ True)) ∨ p1)) ∨ True) ∧ p1)) ∨ p5))) ∨ ((False → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116690422368247935473616461659 : (((True ∧ p5) ∨ ((((p1 ∨ p4) → p1) → (((False ∨ (p4 → (p3 ∧ (False → p3)))) → p3) ∧ (p4 → p4))) → (p5 ∧ p3))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344423873196707395342297665349 : (p2 → (p5 ∨ ((p1 ∨ ((((((p3 ∨ p4) ∧ False) ∨ False) → p1) ∧ (True → ((p2 ∨ False) ∧ p2))) → (p4 ∨ p4))) ∨ (p1 → (p2 ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61320491462074443335608047337 : ((False ∧ (p4 → ((False → ((p1 ∨ ((((p4 → True) ∧ p1) ∧ (False ∧ p5)) → (False ∧ ((True ∨ (p1 ∧ True)) → p3)))) ∨ p4)) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147934741123094432294230495382 : (((((False → (True ∨ p2)) ∨ p1) → (p2 ∧ (((p2 ∨ p1) → (p1 → (p5 ∧ False))) → False))) ∧ (p5 ∨ True)) ∨ (False → (p1 → (p5 ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184082968602565706979828967752 : (((((False ∧ p2) ∧ p3) ∧ ((p4 ∧ False) ∧ (p1 ∨ True))) ∨ p1) ∨ (p1 → ((p4 ∨ ((p2 → p2) ∨ (p5 → p2))) ∧ ((p5 ∨ False) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_565908807132609171163459532439 : (((True → ((((True → p2) → (((p1 ∧ True) ∧ p3) ∨ p3)) → (False ∨ p4)) ∨ ((p3 ∧ p3) → (((True ∧ (p5 → p5)) → True) → True)))) ∧ True) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680640387283023906324853083558 : (((((((p4 → (p3 → False)) ∨ False) ∨ False) ∨ ((True ∧ p5) ∨ (((p4 ∧ (p4 → p1)) → p3) → p3))) → (p3 ∨ ((True ∧ p4) ∨ True))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
        -- False on the left can always be used.
        apply False.elim h5
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60460193196297196496647164138 : (((p5 → p2) → ((p1 → ((False → (p2 ∧ (((p5 → p3) → p1) → p1))) ∧ p4)) ∨ ((p4 → (False → (p4 ∧ p4))) → (p1 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147228550541275076614018579973 : (((((((p4 ∨ (p5 ∨ (((p4 ∧ p3) ∧ ((p4 ∨ p5) ∨ p4)) → p5))) ∨ p1) → False) ∧ p3) ∧ p2) ∨ p2) ∨ ((p3 → p1) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40199863238317655981413936876 : (((((p3 ∧ p3) ∧ (((False → p3) ∧ (p4 → (p1 ∧ (p2 ∨ False)))) ∧ (((p4 → p2) → (False ∧ p5)) ∧ (p1 → p2)))) ∧ p2) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62192640827319819385883635839 : ((p3 ∧ (((((p3 ∧ p2) ∧ (False ∨ ((((p4 ∧ (((True ∨ True) ∨ True) ∨ p3)) ∧ False) ∨ p3) ∨ p5))) ∨ p5) ∨ (p1 ∧ p5)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207673128787811155557799662472 : ((((p2 → True) ∨ (p2 ∧ p2)) → False) → (((((False ∨ ((p3 ∧ (p1 → p4)) → ((p5 ∧ False) ∧ p5))) ∧ p4) ∨ p5) ∨ False) ∨ (p5 ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 → True) ∨ (p2 ∧ p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185945772692524287609059092601 : ((((p4 ∧ True) ∨ ((p4 ∨ True) → (False ∧ (p5 → p3)))) ∧ p4) → (((True ∨ p1) → (p2 ∨ p1)) ∨ ((p2 ∧ (p3 ∧ (True ∨ p5))) → p2))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h14 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : (p4 ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- We need to get the left conjuct of h16 based on <expert-advice>.
    let h17 := h16.left
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233889341863099536717222984469 : ((p4 ∨ (p3 ∨ True)) → (((((p4 ∧ (p5 ∧ p2)) → p2) → p4) → False) ∨ ((p4 ∧ p3) → (((p5 ∧ p1) ∨ (p4 ∧ (p1 → p1))) ∨ p2)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h10
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h15
      -- Implications on the right can always be decomposed.
      intro h17
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58882958486560753298427237501 : (((False ∧ p1) ∨ (p5 → ((((p2 ∧ True) ∨ ((p1 ∧ (p1 ∧ (p2 → p3))) ∧ p1)) → (((p4 ∧ False) → p4) → (p4 → p3))) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38864853271920250873099258317 : ((((p1 ∨ (p3 → True)) ∧ (((p2 ∨ p1) ∧ p3) ∧ ((p1 ∨ p5) ∧ (((p5 → (p3 ∧ (p1 → p1))) ∨ p2) → (p5 → p5))))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188672888628294378296877817446 : (((p1 ∧ (p3 ∧ ((p4 ∨ False) ∧ p5))) ∨ (p5 → p5)) ∧ ((p5 → (p1 ∨ (((False ∧ p3) → (False → (p5 → True))) ∧ (p5 ∧ p4)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225944342486595250091204465556 : (((p2 ∧ p4) ∨ False) ∨ (((((p4 → ((p3 ∨ p3) ∧ (p1 ∧ (((p2 ∧ p1) ∧ True) → (True → False))))) ∧ (p1 ∨ p4)) → p4) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_13354693453996550447566626194 : (((True → (((p4 ∨ ((p1 ∧ p5) → ((p5 ∧ p3) ∧ False))) ∧ (False ∧ p4)) ∧ (p2 → (p3 ∧ (((p4 → p2) → False) ∧ p2))))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243449086398324206631097607674 : ((p5 → True) ∧ (p1 → ((((((True ∧ False) → p5) → p4) → ((p1 ∨ p3) → False)) ∧ p4) ∨ (p4 → ((False ∧ (p5 ∨ True)) ∨ (p1 ∨ p2)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117566854095490197479065444979 : ((p2 ∧ ((((p1 ∧ p4) → p5) ∨ p4) → ((((p5 ∨ (p2 → ((False ∨ p1) ∧ p4))) ∧ p5) → ((p5 ∨ p1) → p4)) ∧ p1))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160354426914092951398311295648 : ((((False ∨ (p3 ∧ ((True ∧ ((True → p4) ∧ True)) → (p1 ∧ p2)))) ∧ p5) ∧ ((p4 → p3) ∧ p2)) → (p4 ∨ ((p2 ∨ (p2 ∧ p1)) ∨ False))) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209294515362009015487255421934 : ((True → ((p3 ∧ p4) → (p4 → p2))) → (((p3 → p4) ∧ (((p1 → False) ∧ True) ∧ True)) ∨ ((p3 → False) ∨ (False ∨ ((True → False) → p1))))) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317748399684686168373183547745 : (p4 ∨ ((((p4 ∨ (p1 ∧ ((((p5 ∨ p5) ∧ p4) ∧ (((p5 ∧ p5) → False) ∨ p2)) ∨ p1))) ∨ False) ∨ ((False ∧ p2) → (p5 ∨ p2))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_117659230053928243107353433990 : ((p3 ∧ (((True ∧ p3) ∨ ((((p1 ∧ p4) ∧ (p4 ∨ (p5 ∧ (p1 → p2)))) ∧ True) ∧ (True ∨ p2))) ∧ ((False ∨ True) ∨ p4))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172718819076697528020976782234 : (((p5 ∨ p2) ∨ (((p1 ∨ ((p5 ∧ p5) ∧ True)) → (True → (False ∧ True))) ∨ p3)) ∨ (True → ((p3 ∧ ((True ∧ (p2 ∧ p5)) ∧ p4)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305413086116573446652584708969 : (p1 ∨ (((p5 ∧ p5) ∨ (((True ∧ p3) → True) ∧ (p5 ∨ (p2 ∨ ((p4 → p3) → True))))) ∨ (p4 ∧ (((p3 ∨ p1) ∨ p2) ∨ (p3 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309907687367445385229466076350 : (p2 ∨ ((((((True → ((False → p3) ∧ ((True ∨ p4) → p4))) ∨ (p5 ∨ p2)) → p1) ∧ p2) ∧ p4) ∨ ((p4 → p4) ∨ ((True → p1) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167693694786363826452603422541 : (((((((True → p5) ∨ p3) → False) ∧ p2) ∧ (p4 ∧ (p5 ∧ p5))) ∧ ((p5 ∨ True) → True)) → (p5 → (((p2 ∧ False) ∨ p1) ∧ (p2 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h6.left
  let h10 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h13 : ((True → p5) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h14
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h15 := h7 h13
  -- False on the left can always be used.
  apply False.elim h15
  -- Implications on the right can always be decomposed.
  intro h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314742787559112325108399080041 : (p3 ∨ ((((p1 ∨ ((p1 ∨ (p1 ∧ (p4 ∧ p5))) ∧ p5)) ∧ False) ∨ (p5 → True)) ∨ ((p3 ∧ p2) ∧ (((p4 → p5) → (p3 → False)) → True)))) := by
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
theorem thm_5_vars_204807780603314250834814491730 : (((((p2 ∧ p3) ∨ p1) ∨ p4) → p3) ∨ (p3 ∨ (True → (p5 ∨ (((p4 ∧ (p2 ∨ p3)) ∨ (False → p5)) ∨ ((p2 ∨ (False → p2)) ∧ True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382577292824057181620298115223 : ((((((False ∧ ((p2 ∧ p3) ∨ (p3 ∧ p3))) ∨ (((((True ∧ ((True → p4) ∧ p1)) ∧ p3) ∨ p3) → (p1 → p4)) ∧ p5)) ∨ False) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_147420955824732882985059287802 : (((((False → False) → True) ∧ (p5 ∨ (((p5 → (p5 → (p3 ∨ (False ∧ (True ∧ p2))))) ∧ True) ∧ False))) ∨ p1) ∨ ((p5 ∨ (False ∨ True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_624641282855285048476937210572 : ((((p4 ∨ ((p2 ∨ (p3 → p1)) → (((((p2 ∧ ((p4 ∧ p2) ∨ True)) → p5) → p5) ∨ p3) ∨ (((p2 ∧ True) → p3) → p5)))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_171629152631378978965078055528 : ((((p4 ∨ (p3 → p5)) → (p3 ∨ ((((p2 ∨ p1) ∨ p2) ∧ p1) ∨ p3))) ∨ p3) ∨ (p1 ∨ ((p2 → (p2 ∨ p3)) ∨ ((p1 → True) → p2)))) := by
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
theorem thm_5_vars_134119214267174997140346408375 : ((((((True ∨ (p2 ∧ (False → p1))) → (p5 ∨ ((True ∧ p3) ∨ (p4 ∧ (p5 → p2))))) → p5) ∨ (True ∧ p3)) ∨ p3) ∨ (p2 ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246349062337875548950431774667 : ((p4 ∧ p5) ∨ ((p2 → p4) ∨ ((((p1 ∨ (True ∨ p4)) → (p3 ∧ p2)) ∧ ((p4 ∧ ((p4 ∨ p4) ∧ p3)) ∨ p3)) → (p2 ∨ (True ∧ p5))))) := by
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
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : (p1 ∨ (True ∨ p4)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h14 : (p1 ∨ (True ∨ p4)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h15 := h2 h14
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h18 : (p1 ∨ (True ∨ p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h19 := h2 h18
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164580113187936851377195924425 : ((((p4 ∨ (p5 → p4)) → (p5 ∧ (p3 ∧ (((p5 ∧ p3) ∨ p5) → (p3 ∨ p3))))) ∧ p4) ∨ (p3 → (p2 ∨ ((True → p2) → (p4 → p3))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358733211576429273391982693758 : (p5 → (p5 → (((p2 ∨ p1) ∧ p5) → ((((((p4 → p3) ∨ p1) ∨ True) ∧ (True → ((p3 ∧ True) ∧ (p4 ∧ p5)))) → p4) ∨ (True → False))))) := by
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
  cases h4
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h12 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h13 := h9 h12
        -- We need to get the right conjuct of h13 based on <expert-advice>.
        let h14 := h13.right
        -- We need to get the left conjuct of h14 based on <expert-advice>.
        let h15 := h14.left
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h17 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h18 := h9 h17
        -- We need to get the right conjuct of h18 based on <expert-advice>.
        let h19 := h18.right
        -- We need to get the left conjuct of h19 based on <expert-advice>.
        let h20 := h19.left
        -- One of the premise coincides with the conclusion.
        exact h20
    case inr h21 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h22 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h23 := h9 h22
      -- We need to get the right conjuct of h23 based on <expert-advice>.
      let h24 := h23.right
      -- We need to get the left conjuct of h24 based on <expert-advice>.
      let h25 := h24.left
      -- One of the premise coincides with the conclusion.
      exact h25
  case inr h26 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h27
    -- Conjunctions on the left can always be decomposed.
    let h28 := h27.left
    let h29 := h27.right
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
        have h32 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h29, we can now drive its conclusion.
        let h33 := h29 h32
        -- We need to get the right conjuct of h33 based on <expert-advice>.
        let h34 := h33.right
        -- We need to get the left conjuct of h34 based on <expert-advice>.
        let h35 := h34.left
        -- One of the premise coincides with the conclusion.
        exact h35
      case inr h36 =>
        -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
        have h37 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h29, we can now drive its conclusion.
        let h38 := h29 h37
        -- We need to get the right conjuct of h38 based on <expert-advice>.
        let h39 := h38.right
        -- We need to get the left conjuct of h39 based on <expert-advice>.
        let h40 := h39.left
        -- One of the premise coincides with the conclusion.
        exact h40
    case inr h41 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h42 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h43 := h29 h42
      -- We need to get the right conjuct of h43 based on <expert-advice>.
      let h44 := h43.right
      -- We need to get the left conjuct of h44 based on <expert-advice>.
      let h45 := h44.left
      -- One of the premise coincides with the conclusion.
      exact h45



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112254265600192187219846145432 : (((p4 ∨ (((p5 → (((p5 ∨ (p2 → True)) → p3) ∧ (p3 ∧ (True ∨ True)))) → (False → True)) → ((p2 ∨ p4) ∨ p1))) ∨ True) ∨ (p5 → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784878917071308661047890285499 : (((p3 ∨ (p2 → ((((True ∨ p2) ∨ (((p5 ∨ (True → (p2 ∨ (((p3 ∧ False) ∨ p2) ∧ p5)))) ∧ (False ∨ True)) ∧ True)) ∧ p3) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165478802151969796128407958902 : ((((((p4 ∧ p5) → True) → ((True → p1) ∨ p2)) ∨ False) ∨ (p5 ∨ ((False ∨ p5) → p4))) ∨ ((False ∧ (p5 ∧ (p1 ∧ (False ∨ p1)))) → p5)) := by
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
theorem thm_5_vars_84181244783403105226886500539 : (((p1 → ((p1 ∨ (p4 ∨ (((True → p2) ∧ ((p3 ∧ p3) ∨ p5)) ∨ p1))) → p5)) ∧ ((True ∨ p3) → (((p3 ∧ p1) ∧ False) ∧ True))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757270564966628975279362855797 : (((p1 ∧ ((True ∧ False) ∨ (((False ∨ (p1 ∧ (p5 → p3))) ∧ (p5 ∧ p1)) ∨ ((p3 → ((p1 → (p3 ∧ p2)) ∨ (p5 ∧ False))) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136860093434022894436686557153 : (((p5 ∧ p2) ∨ (True → ((False ∧ p2) ∨ (((p1 ∨ (p3 ∧ (p2 → p1))) → (p5 → (p1 ∨ (p5 ∨ p4)))) ∧ True)))) ∨ (False → (True → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343252562470155481088233973051 : (p2 → ((p3 → (p4 ∧ False)) → ((((p5 ∨ p5) → (True → (((((p4 ∧ p5) → (True → p5)) ∧ (p1 ∨ p4)) → p3) ∧ p1))) ∨ p1) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258828033942402454876485636016 : ((True → p1) → ((p5 ∨ (True ∧ ((p5 ∧ ((p4 ∧ p1) ∨ (((((p3 → p4) ∨ False) → p1) → (True ∨ (p4 ∨ p4))) ∧ p2))) ∨ p4))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49587440744900425620471867488 : (((((p3 → p5) ∨ ((p2 ∨ (False → False)) ∨ ((p1 ∧ p2) ∧ p3))) ∧ (False ∨ ((p2 ∧ p4) ∨ (p4 ∧ p1)))) → (True → (p5 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180144825347645681055890840539 : ((((p5 → (p3 ∧ (True → (False ∧ ((p1 → p3) ∧ p4))))) → False) → p3) → (p3 ∨ ((p2 ∨ (((False ∧ p1) → (True ∨ p4)) ∨ p5)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42969491651914973076614599233 : (((p5 → (((((p4 ∧ (True → ((p3 ∨ ((p4 ∧ p3) ∨ p4)) ∨ p5))) ∨ p4) ∨ True) ∨ ((p4 ∧ p5) → p4)) ∧ (False ∨ p5))) ∨ False) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310111333474994728899509774086 : (p2 ∨ (((((p2 → p5) ∧ p1) ∧ (p3 ∨ (((p4 ∨ p5) ∨ p4) ∧ p5))) ∧ p5) ∨ ((False ∨ (p1 ∨ ((False → p4) ∨ (p2 → p4)))) ∨ p4))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793555644818507631865339465546 : (((True → (p2 ∨ (False ∧ ((p1 ∧ ((((False ∨ p4) ∨ p2) → (False ∨ (((p3 → (True → p1)) → p2) ∧ True))) ∧ (p5 ∨ p2))) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339664440630255479967771154465 : (p1 → (p3 ∨ ((((p4 ∨ p1) ∧ (False ∧ (p2 → (p4 ∨ (True → (p3 → p4)))))) ∨ ((p1 ∨ (p5 ∧ False)) → ((p4 → p4) ∨ True))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136635930065242082397666431877 : ((((p1 → p2) ∨ p4) → ((((p1 ∧ (p2 ∧ (p3 ∧ (((p3 → (p1 → p2)) ∨ p2) → p1)))) ∨ p2) → p3) ∨ p5)) ∨ ((p2 ∧ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797572467624610132548699108559 : (((p1 → (((((p2 ∨ ((p2 → (p4 ∧ ((p5 → (False ∧ p5)) → (True ∨ (p4 ∧ True))))) ∨ p3)) ∨ False) → False) ∨ (True → p4)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745824236494990968697646368328 : ((((False ∨ p1) → (((((((False ∨ p2) → p1) → (((p1 → p4) → p5) ∧ False)) → ((False ∨ (p5 → p4)) ∧ False)) ∧ False) ∨ p4) ∨ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589548157601121915998891056555 : ((((((((True ∨ p4) → ((True ∧ (((p5 ∧ p1) ∧ ((p3 ∨ p2) ∧ p5)) ∧ ((p3 → True) → p2))) ∧ p1)) → p2) → False) → False) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669153912297800995616757115812 : (((((((p2 ∧ True) → (p3 ∧ p4)) ∧ ((p3 ∧ (((p1 ∧ False) ∧ ((p5 → False) → p2)) ∨ p1)) ∨ p3)) → p1) ∨ (p2 → (False → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698761095167720506098072159467 : (((((p5 ∨ False) ∨ (((p5 ∨ (p1 → p2)) → p1) ∨ (p4 ∧ p4))) ∨ ((False → ((((p1 → (p3 ∧ p5)) ∨ p4) → True) ∧ p2)) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_616576462884299749291376790412 : ((((((p3 → ((((p3 → p2) → p4) → p5) → p1)) → False) ∧ ((p1 ∨ (p4 ∨ (((p4 → p3) ∨ p1) → (True ∧ False)))) ∨ p3)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78700722480913838947083443935 : (((((p1 → p5) ∨ ((((p1 → (True ∨ p4)) ∨ (p2 → p2)) ∧ True) ∨ p4)) ∧ ((p4 ∧ ((p4 ∧ p3) ∨ p1)) ∨ True)) ∧ (True → False)) → p2) := by
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
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h13 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h14 := h3 h13
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h17 := h3 h16
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h20 := h3 h19
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h26 =>
          -- Conjunctions on the left can always be decomposed.
          let h27 := h26.left
          let h28 := h26.right
          -- Disjunctions on the left can always be decomposed.
          cases h28
          case inl h29 =>
            -- Conjunctions on the left can always be decomposed.
            let h30 := h29.left
            let h31 := h29.right
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h32 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h33 := h3 h32
            -- False on the left can always be used.
            apply False.elim h33
          case inr h34 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h35 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h36 := h3 h35
            -- False on the left can always be used.
            apply False.elim h36
        case inr h37 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h38 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h39 := h3 h38
          -- False on the left can always be used.
          apply False.elim h39
      case inr h40 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h41 =>
          -- Conjunctions on the left can always be decomposed.
          let h42 := h41.left
          let h43 := h41.right
          -- Disjunctions on the left can always be decomposed.
          cases h43
          case inl h44 =>
            -- Conjunctions on the left can always be decomposed.
            let h45 := h44.left
            let h46 := h44.right
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h47 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h48 := h3 h47
            -- False on the left can always be used.
            apply False.elim h48
          case inr h49 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h50 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h51 := h3 h50
            -- False on the left can always be used.
            apply False.elim h51
        case inr h52 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h53 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h54 := h3 h53
          -- False on the left can always be used.
          apply False.elim h54
    case inr h55 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h56 =>
        -- Conjunctions on the left can always be decomposed.
        let h57 := h56.left
        let h58 := h56.right
        -- Disjunctions on the left can always be decomposed.
        cases h58
        case inl h59 =>
          -- Conjunctions on the left can always be decomposed.
          let h60 := h59.left
          let h61 := h59.right
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h62 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h63 := h3 h62
          -- False on the left can always be used.
          apply False.elim h63
        case inr h64 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h65 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h66 := h3 h65
          -- False on the left can always be used.
          apply False.elim h66
      case inr h67 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h68 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h69 := h3 h68
        -- False on the left can always be used.
        apply False.elim h69



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44218293731717340311202885983 : ((((((p5 ∨ ((p1 ∧ (p1 ∨ (p4 ∧ (False ∧ (p5 ∧ (p3 ∨ p2)))))) → p5)) → p5) ∧ p1) ∨ (p3 ∨ (p2 ∨ (p3 → p2)))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184100739920153297701551509516 : ((((p4 ∧ p2) ∧ ((p1 ∨ (p2 ∧ (p3 → p4))) ∧ p5)) ∨ True) ∨ (((True ∧ (p3 → (p1 ∨ (p2 ∨ p4)))) → p3) ∧ (p4 ∧ (p5 ∨ True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205114307095498969609197613206 : ((((p1 ∨ p2) ∨ True) ∧ (p3 → p1)) ∨ (((p5 ∧ ((False → p2) → p2)) ∨ (p2 → (True ∨ (((p4 ∧ p2) ∨ p5) ∨ (p5 → True))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66107706258941522908340090420 : ((p5 ∨ (((((p3 ∨ p2) ∧ p5) ∧ False) ∨ ((True → (True → p3)) ∧ (p2 ∨ ((False → (((False → p4) ∨ p4) → p1)) ∧ p5)))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357263746660463378793193793582 : (p5 → ((p2 ∧ p2) ∨ ((p2 ∨ (((False ∧ (p5 ∧ p5)) ∧ p3) ∨ ((p2 ∨ p1) → ((p3 → p3) → p4)))) ∨ ((p3 ∨ (True ∨ False)) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_57644265627276335196400472149 : ((((False ∨ True) ∨ p4) → ((False → True) → ((((p5 ∧ (((False ∧ True) ∨ p3) ∧ p4)) ∧ True) ∨ True) → (p2 → (False ∧ (p5 → False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55578345047580360762899983855 : (((p1 ∨ (((p2 → p3) ∨ p5) → p3)) → (True ∧ (True → (p5 → ((False ∨ False) ∨ (p2 ∧ (p1 ∧ (False ∨ (False ∧ (p3 → p5)))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111383268921961117439666187173 : (((False ∨ (((False ∨ ((p4 → False) → False)) → (p4 → (((p1 ∨ p1) ∧ p3) ∨ (p3 ∧ p1)))) ∧ (True ∧ (True ∧ p2)))) ∧ True) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244604858397905418189505684609 : ((False ∧ p4) ∨ (p3 → (p1 ∨ ((p5 ∨ ((p2 ∧ p2) ∧ p2)) ∨ ((True ∨ (True ∧ ((p3 ∨ (p2 ∧ p2)) → True))) ∨ ((False ∨ False) → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_797658411355288821472384285343 : (((p1 → (((False → (True ∨ False)) ∨ (((True → True) ∨ p3) ∧ (((p3 ∨ (p3 ∧ (p2 ∧ p4))) → (True ∨ p4)) ∨ (False ∨ p1)))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160100255268678617630571131553 : (((True → (((p2 ∨ (p1 ∧ p4)) ∨ True) ∨ ((False ∨ p5) ∨ ((p2 ∧ False) → (p3 ∨ False))))) → False) → ((p5 → p4) ∧ ((False ∨ True) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (True → (((p2 ∨ (p1 ∧ p4)) ∨ True) ∨ ((False ∨ p5) ∨ ((p2 ∧ False) → (p3 ∨ False))))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206420307584175609195225812424 : ((p3 ∨ (p4 ∨ ((False ∨ p4) ∧ False))) ∨ (True ∨ ((p3 ∨ p3) → (((p1 ∨ (p1 ∧ p5)) ∨ (p4 ∨ p1)) ∨ (p1 → (p1 → (False ∨ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262314406024554405990313095147 : (True ∧ (((False ∧ (((p3 ∨ p2) → p2) → ((True → True) → p2))) ∨ (p2 ∨ ((p2 → p2) ∨ ((p3 ∨ (p1 → p4)) ∧ (p5 ∨ p4))))) ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173400285124958931364899863470 : ((p4 → (p3 ∨ (((p1 → (p2 → (p1 ∧ (p3 ∨ p4)))) ∨ (p1 → p2)) ∧ p1))) ∨ (((p4 ∧ (True ∨ True)) ∨ (p5 → p5)) ∨ (p3 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42565359858975989456296158307 : (((p2 ∨ ((((p1 ∨ (True ∨ p4)) → ((p3 ∨ (((((True ∧ p5) ∨ (p1 ∨ p5)) ∨ True) ∨ False) ∧ p5)) ∧ False)) → False) ∧ True)) ∨ p2) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ (True ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653612271214135545468986712043 : ((((((p5 → ((p4 ∧ (p5 ∨ (((p1 ∨ p5) ∨ p1) ∨ (p1 ∨ ((p5 ∨ (True ∨ p2)) ∧ p1))))) ∨ p1)) ∧ p2) ∧ p1) ∨ (p1 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217762550787496933038778573423 : (((p4 ∧ (p5 → p3)) → p4) → (((p3 ∧ p4) → (p3 → ((True → (p5 ∨ (p4 ∧ True))) → p5))) ∨ ((False ∨ False) → (p4 ∧ (p2 ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647036830837942808987228339513 : ((((p3 → (((((p2 ∧ False) ∨ (((p5 ∧ p4) ∨ (p5 → p1)) → False)) → p4) → ((p2 ∨ p3) ∨ (p5 → p3))) ∨ (p3 → p3))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350134655039041220439966500675 : (p4 → (((p5 ∨ ((((((True ∧ p1) ∧ p2) ∧ True) ∧ p5) ∨ p5) ∧ (p4 ∧ p3))) ∨ ((False → (p4 → ((p1 → False) ∨ False))) → p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158500764133089746277324488213 : (((p5 ∧ p1) → ((p3 ∧ ((((p5 ∧ p3) → (p3 ∧ ((False ∧ p2) ∨ p3))) ∧ False) ∨ p3)) ∨ p1)) ∨ ((p2 ∨ (p4 → p3)) → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356263189081688890071200107207 : (p5 → (((((p5 → p4) ∨ p5) ∨ p4) → (((False ∧ (True ∨ p5)) → (False → p4)) → p2)) ∨ (((p4 ∧ p5) → ((True ∧ True) → p5)) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318633766207926226484197567668 : (p4 ∨ ((p3 ∧ ((p5 ∨ (((p4 → False) → p1) ∧ True)) ∧ (((p1 ∧ (p3 → p2)) ∨ ((p2 → (p1 ∧ p3)) → p5)) ∧ p4))) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



