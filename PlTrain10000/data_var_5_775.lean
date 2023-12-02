variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165007698782012573574545111766 : (((((False ∨ ((p4 ∨ True) ∧ True)) ∨ p2) ∨ (p4 → (True → (p4 ∨ (True ∨ p5))))) → p2) ∨ ((True ∨ (((False ∧ p3) ∨ p5) → True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211386771219696216418305082884 : (((False → p2) ∨ (False ∨ p5)) ∧ ((p3 → (True → p3)) → ((p2 ∧ (p4 → (((False ∧ p3) ∧ (p2 → True)) ∧ ((p2 → p5) → True)))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780305036060828693751090725075 : (((p2 ∨ (((((p1 → (((p1 → ((p5 ∧ p3) ∧ p3)) ∨ p2) ∨ p3)) ∧ p3) → (p2 ∧ p2)) ∨ p2) ∨ (p4 → (False → (p2 ∧ p2))))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41765401182839389209433118735 : ((((True ∧ (p2 ∨ (p3 ∧ True))) ∨ (False ∨ (p2 ∧ (p2 ∧ ((False → (((False ∧ p5) ∧ p1) → (p4 ∧ (p1 ∧ p5)))) → p3))))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138028068830107767511344853475 : ((True → (((((False ∧ p1) ∨ p2) ∨ (p1 → False)) → (False ∧ (p1 ∧ ((p3 → (p5 → p1)) ∨ p5)))) ∨ (p4 → True))) ∨ (p2 ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698460609238287847336100642052 : ((((((False ∨ (p4 ∨ p4)) → (p5 ∧ False)) ∨ ((p3 ∧ p3) ∧ False)) ∨ (True ∧ ((False ∧ False) → ((False ∧ p3) ∧ ((p5 ∨ False) ∧ p1))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234453529999243164749201376454 : ((p2 → (p5 ∧ p1)) → (p2 ∨ (((True ∧ (((p2 ∧ (((p3 → p3) ∨ p5) ∧ (False ∨ p2))) → (p1 ∨ p4)) ∧ p2)) ∨ p5) ∨ (p4 ∨ True)))) := by
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
theorem thm_5_vars_152781648867330787020638433574 : (((p1 ∧ p3) → (p4 ∧ ((((True ∨ (p5 ∧ ((True ∧ True) ∧ p3))) → (p3 ∧ p2)) ∨ (p2 → p5)) → p1))) → (p4 ∨ ((False → p2) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178270725238770719810114429489 : (((((p2 ∧ False) ∨ p1) ∧ (p1 ∧ ((p3 → p3) → p1))) ∧ (p3 → p4)) ∨ (False → ((p3 → ((p2 → False) ∧ (p2 → (p5 ∧ p3)))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810680234182307115320053796282 : (((p5 → (((p3 ∨ p2) ∨ p1) ∨ (p2 ∧ (((p1 ∨ p3) ∨ (((p5 ∨ p5) → (True → p1)) ∨ ((False ∨ (p4 ∨ False)) ∧ p1))) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147302580796937993699664863107 : (((((((p2 ∨ (True → ((False ∨ p2) ∨ True))) ∧ p5) ∨ (p1 ∨ p3)) ∨ (p5 → (True → False))) → p3) ∨ False) ∨ (((p3 ∨ p5) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355937095198665413910089218109 : (p5 → (((p5 ∧ p5) ∧ (((p4 ∨ p5) ∨ (((False → p5) ∧ p1) → (p4 ∨ (True → p3)))) ∨ ((p3 ∧ p1) ∧ p2))) → ((p4 → p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55127042243285119229400099766 : ((((p1 ∧ ((True → p3) ∧ False)) ∧ p1) ∨ ((p2 ∨ ((False → (((((p3 → (p4 ∧ True)) ∨ True) ∨ p2) → p1) → True)) ∨ p5)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681945025082287630316444398831 : (((((((True ∧ p5) ∧ ((p5 ∧ p1) ∨ (p4 ∧ (p4 ∨ ((True ∧ True) → p4))))) → p2) ∨ p4) ∧ ((p1 ∧ (p2 ∨ (p5 ∨ p1))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165151490282074206036596748989 : ((((((p4 → p4) ∨ (p4 ∨ p2)) ∧ (True → p2)) → (True → (True ∨ p3))) ∧ (p4 ∨ p3)) ∨ (p5 ∨ (p5 ∨ (p3 → (True → (p1 ∨ p3)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262289055039134929836648134454 : (True ∧ ((((p3 ∨ (p4 → (p3 → True))) ∧ ((p5 → (p5 ∧ (p2 → p5))) ∧ (p2 → True))) → ((p2 ∨ ((True → True) ∧ p2)) → p5)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41307024270087376986470080733 : (((((((p2 ∨ ((p5 → ((p1 → p4) ∨ p2)) ∨ (p2 ∧ True))) → p1) → p3) ∨ p1) ∧ ((((p4 → p5) → p2) → p1) → p4)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260789024014688813080992143015 : ((p3 → p5) → (((((p2 → p1) ∧ (p2 ∧ False)) ∨ (p2 → (p2 ∨ True))) → (False ∨ False)) ∨ ((p4 ∧ True) ∨ (p2 → (True ∨ (False ∧ True)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800967691609580079316447479029 : (((p2 → ((p4 → ((p4 ∧ (True → ((False → (False ∨ p1)) ∨ (False ∨ p1)))) ∨ (((False → p2) → (p2 → p2)) ∨ p5))) → (p3 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56431734618045718037817520369 : ((((False → p4) ∧ (p4 → p3)) → (((False → p3) → p4) ∨ (p5 → (((p5 ∨ (p4 → p2)) ∧ (p4 ∨ ((True ∨ p5) ∧ False))) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55310971450222470731433871265 : (((False ∨ (((p2 → False) ∧ p4) ∧ True)) ∨ ((p1 ∧ p2) → ((((False ∨ ((p2 ∧ p1) ∧ (p5 → False))) → p4) ∨ (p1 ∧ p1)) ∨ False))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121842191912810897829734570018 : ((((p5 ∨ p4) ∨ ((p1 → p4) ∨ (p2 ∨ ((p4 ∧ False) → (p2 ∨ (p3 ∧ ((p5 ∧ ((p2 ∧ p3) ∧ False)) ∨ p2))))))) → p3) → (p3 ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∨ p4) ∨ ((p1 → p4) ∨ (p2 ∨ ((p4 ∧ False) → (p2 ∨ (p3 ∧ ((p5 ∧ ((p2 ∧ p3) ∧ False)) ∨ p2))))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687040717524380766801812569669 : ((((p5 ∨ (p5 → (False → (((((p2 → (p1 ∧ (p5 ∨ p2))) ∨ p3) ∨ False) ∨ p3) ∨ p2)))) → (p2 → (p2 → (True ∧ (p5 → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264904836014852979001287355905 : (True ∧ ((True ∧ p3) → (((False ∧ False) ∨ (p3 ∨ ((False → ((p1 ∧ (False ∨ False)) → True)) → p1))) ∧ (p2 ∨ ((p1 ∨ False) ∨ (p2 ∨ p3)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759031454603377364504561189353 : (((p2 ∧ ((False ∨ (((True → ((True → True) → p5)) → p1) ∧ (p1 ∨ (((p5 ∧ True) → (p2 ∧ (p3 → p3))) → (p4 → True))))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670667168157371137354307980771 : (((((p5 ∨ p1) → ((p5 ∨ (p5 ∨ (((((((p2 → p3) → p4) → True) ∨ p3) ∨ True) → p2) ∨ p1))) ∧ True)) ∨ ((p3 → p1) → p3)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308332065798669275495324999982 : (p2 ∨ (((((((((True → p1) → (p4 → p3)) → True) ∧ p1) ∧ (((p5 ∨ (p4 ∧ p5)) ∨ p4) ∨ p4)) ∨ (p1 ∧ p1)) ∨ p2) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328928772556806639482015502010 : (True → ((p3 ∧ (p5 ∨ ((p2 → p1) ∨ (p1 ∨ p4)))) → ((False ∨ ((p3 → p4) → p2)) → (((p1 → False) ∧ p1) → (p2 ∧ (False → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h2.left
    let h10 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h12 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h13 := h5 h12
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h16 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h17 := h5 h16
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h20 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h19
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h21 := h5 h20
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h23 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h6
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h24 := h5 h23
          -- False on the left can always be used.
          apply False.elim h24
  -- Implications on the right can always be decomposed.
  intro h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58400901182349032830254847780 : (((p2 ∨ False) ∧ ((p4 ∧ ((p1 ∨ p5) → (((p2 ∨ (((True → (p4 ∧ False)) ∧ True) ∨ False)) ∧ p3) → ((p3 → p3) ∧ p5)))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309793989861847179587537481087 : (p2 ∨ (((p5 → ((p3 → ((p2 → False) ∨ False)) ∨ (p2 ∧ (p1 ∧ ((p3 ∧ p3) ∧ p1))))) → (p1 ∧ True)) ∨ (p1 → ((True ∨ False) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637229246999730119692360443838 : (((((((((p4 ∧ (False ∨ False)) ∨ True) ∧ (True → p4)) ∧ True) ∨ False) → ((p1 ∨ p1) → (p4 ∨ ((p5 ∧ (p2 ∨ True)) ∨ p2)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174417986127997972438824086628 : ((((p3 ∧ p3) ∧ (((True ∧ True) ∧ p5) → p1)) ∨ (p5 → ((False ∧ True) ∨ p2))) → ((((((p4 ∧ p1) ∧ p1) → p3) ∧ p3) ∨ p2) ∨ True)) := by
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
theorem thm_5_vars_696799373297811501234188410998 : (((((p1 ∧ ((p5 ∧ (False ∨ True)) → (True ∨ (p1 → p1)))) → p5) ∧ ((False ∨ (((p3 ∨ p1) ∧ (False ∧ False)) ∧ p3)) → (p3 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193610942499887949671133943706 : ((True ∧ ((True ∧ (p5 → ((p4 ∨ True) ∧ False))) ∧ p1)) → (((p1 ∧ p4) ∨ ((False ∧ ((p5 → p4) ∧ ((p3 → p3) ∧ False))) ∨ p1)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317598717126661795850886763336 : (p4 ∨ ((((p2 ∧ p4) ∧ ((p5 ∨ (p2 ∨ p3)) ∨ (((False ∨ p5) ∧ ((p4 ∧ p2) → ((p1 ∧ p4) ∧ (p4 ∧ p5)))) → p4))) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734279512219222487911956258668 : ((((False ∨ p1) ∧ (p5 ∧ (((((p1 ∧ (p3 → ((p3 → p1) ∧ p4))) → p1) → ((p1 → p5) ∨ p1)) ∨ True) ∨ (p3 ∨ (p5 ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683183203983773128928214098057 : ((((p5 ∧ ((p3 → ((p5 → (((True → p1) → (p4 ∨ True)) ∧ p5)) ∧ (True ∨ p3))) → p3)) ∧ (True ∨ ((False ∨ (p3 ∧ False)) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42945264337524196144493030006 : (((p4 → ((p4 ∧ p5) ∨ ((p5 ∧ ((p2 ∧ (False ∨ (p4 ∧ False))) ∨ False)) ∨ ((p5 → (p5 ∧ ((p2 → p4) ∨ False))) ∨ p1)))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186447084284404829928137656193 : ((((((p1 ∨ True) → (p1 ∨ p3)) ∨ p5) ∧ p2) ∧ (False → p2)) → (((True ∧ p5) ∨ ((p3 ∧ True) ∨ p4)) ∨ (p1 ∧ ((p4 ∧ p1) → p2)))) := by
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
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (p1 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h13
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356574175720287492991904964655 : (p5 → ((p4 ∨ ((p4 ∨ p5) ∨ (p4 ∧ ((p4 ∧ False) ∨ True)))) → ((((p5 ∧ (False ∨ p1)) ∧ (p5 ∧ p1)) ∨ p5) ∨ ((False → False) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309365744901836587058241999045 : (p2 ∨ (((p1 → (p4 ∨ (False → p4))) → (p3 ∧ ((((p5 → True) ∨ ((False ∨ True) → ((True → False) ∧ True))) ∨ p3) ∧ False))) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193040716355553791822219610194 : (((False ∨ ((False ∧ p4) → (False ∨ p1))) → (True → p4)) → (((p3 ∧ (((True ∨ (((False ∨ p3) ∧ p3) → p4)) → p4) → p1)) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_480381846001289262995642151040 : ((((((True ∧ ((p1 ∧ p5) ∧ p3)) ∨ p1) ∨ p3) ∨ ((False ∧ ((True ∨ True) ∨ (p4 ∨ (((True ∧ p3) ∧ p4) ∨ (p5 → True))))) → False)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696472526459137108314837370013 : ((((((True → (p3 → (False ∨ p3))) → (p3 ∨ (p4 ∨ p1))) ∧ p5) ∧ ((False ∨ ((p5 → ((p1 → (p5 ∧ p4)) ∨ p1)) → p4)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134252752884885220836066763842 : ((((p3 → (p1 → p1)) ∧ ((p5 ∨ ((False ∨ p2) ∨ p3)) ∧ ((((True → p5) ∧ True) ∨ p2) → (p1 ∨ p3)))) ∨ p3) ∨ ((False ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299623840512676001410144965829 : (False ∨ (((p5 → (((p1 ∧ (((p5 ∧ ((((p1 ∨ False) ∧ False) ∨ False) → p1)) ∧ ((p3 → p2) → False)) ∨ p4)) ∨ False) ∨ p5)) → p3) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → (((p1 ∧ (((p5 ∧ ((((p1 ∨ False) ∧ False) ∨ False) → p1)) ∧ ((p3 → p2) → False)) ∨ p4)) ∨ False) ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314963179155157400963077593690 : (p3 ∨ ((p3 ∧ (p4 ∧ ((p3 ∧ p3) → ((p5 ∨ False) → p1)))) → ((((((False → p4) ∨ (p3 ∨ True)) ∧ (p4 → p3)) ∨ p4) ∧ p1) → p1))) := by
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
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h1.left
      let h10 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h1.left
        let h16 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h1.left
        let h21 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h1.left
    let h26 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h27 := h26.left
    let h28 := h26.right
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42243575156374655793694920266 : (((False ∧ (p1 ∨ ((p2 → (p3 ∧ p2)) ∧ (((((((p4 ∧ True) → p5) ∨ (p2 → p2)) ∨ p1) ∨ (p5 → p1)) → p2) ∧ p5)))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41443110074652306017333499624 : ((((p2 ∨ ((p5 → (((p2 → False) ∧ (p3 → (p5 → p4))) → True)) ∨ False)) → ((p3 ∧ ((True ∨ p1) → p4)) ∨ (p4 ∧ p2))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217286571437237497884819647550 : (((p3 ∧ (p1 → p4)) ∨ False) → (p2 ∨ (((p4 → p1) ∨ p2) ∨ ((True ∧ True) → ((p4 ∧ (False ∧ p2)) ∨ (p4 → ((p3 → p5) ∨ p4))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61146573377558209823458771385 : ((False ∧ ((p5 ∨ (False ∨ ((p2 ∨ True) ∧ p4))) → (((((False ∨ p3) → (p3 → p3)) → ((p4 ∨ (p5 ∨ p2)) ∨ p1)) ∧ False) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113762331388110985555005857939 : ((((p4 ∨ ((p5 → (p5 ∧ p3)) → p2)) ∧ ((p1 ∨ True) ∨ (p5 ∧ ((True ∨ p4) ∨ ((p2 ∧ False) ∧ p3))))) → (p2 ∨ p2)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231713916854889941592076501619 : (((p2 ∧ p1) → False) → ((((((True ∨ p2) → p1) → p2) → p2) ∨ ((p2 → p2) ∨ ((True ∧ p5) ∧ p2))) ∨ ((p5 → (p5 ∨ p1)) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191036425578310043282916626712 : ((((p1 → (p5 → p1)) ∨ p5) → ((True ∧ p1) ∧ p4)) ∨ (False ∨ ((p4 ∨ (False → (False ∨ False))) ∧ (p2 → ((p4 → (p4 ∨ p1)) → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133559210795070498608443170401 : ((((((((True ∨ ((p2 → False) ∧ (True → False))) ∨ p3) ∨ (False ∧ (True ∨ p5))) → (p5 ∨ p5)) ∨ p1) ∨ p1) ∧ p5) ∨ (p2 → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340936494657304523986817932928 : (p2 → ((((True ∨ (p2 ∧ False)) → p3) ∨ ((p5 ∨ p1) ∧ (p1 ∨ ((p4 ∧ (((p4 ∧ False) ∨ (False ∧ (True → False))) → False)) ∨ p5)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244674088453868792315275217350 : ((p1 ∧ True) ∨ ((((p5 → ((p5 → p2) ∧ (((True ∨ False) → (p3 ∨ (p2 ∧ True))) ∧ ((p3 ∧ (True ∧ False)) → p2)))) ∨ p4) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10185565087839694484651142108 : (((p1 ∨ (((((False → p3) → p4) ∧ p4) ∧ True) → (True → (((p5 ∧ p2) ∧ p4) → (False ∨ ((p1 ∨ p3) ∨ (p5 ∧ p5))))))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h6
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798841008435796836873082796748 : (((p1 → ((p1 ∨ (p4 ∧ p3)) → (p2 ∨ (((True ∧ p2) → p3) → ((p5 ∧ (((p5 ∧ (p3 ∨ p3)) → (True ∨ p5)) ∧ p3)) ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41673741825054585088615196059 : ((((((p1 ∨ p3) ∧ p1) ∧ (p3 ∧ p3)) ∨ (((p4 ∨ True) ∧ (p3 ∧ True)) → (((p4 → ((p3 ∨ p1) ∨ True)) ∨ True) → True))) ∨ p1) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_228785626787736912118465334998 : ((p3 ∨ (p5 ∧ p2)) ∨ ((((p4 ∧ (p5 ∧ p3)) ∧ ((p2 → p1) ∧ (True ∧ ((((p1 → False) ∧ p1) ∨ p3) ∧ (p2 ∨ False))))) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200265258189178661710016710292 : (((True ∨ (p4 ∨ False)) → ((True ∨ p2) ∨ False)) → ((p3 ∨ p4) ∨ ((False ∧ (p3 → ((p2 ∨ p1) → p5))) ∨ (((False ∧ p1) → p2) ∨ p3)))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185669093101130578981771532301 : ((p1 → (((p5 ∨ ((p2 ∨ (p5 ∧ True)) ∧ p5)) ∧ p2) ∨ p2)) ∨ ((p4 → True) ∨ ((p3 ∨ p4) ∨ ((p1 ∧ p4) ∧ (p1 ∨ (p1 ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136424535365523965277130522064 : (((((True ∧ p5) ∧ False) → p3) → (p2 → ((False ∧ p3) ∧ (p5 ∨ (p5 ∨ (((p3 ∧ (p1 ∨ p4)) → True) ∨ p3)))))) ∨ (True ∨ (True ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341434505005284412916356010043 : (p2 → ((p1 ∧ (((False ∨ (p2 ∨ False)) → (((p5 → p4) → p5) ∨ ((p3 ∨ p5) ∨ True))) → ((p3 → p2) → ((False ∨ p5) ∨ p5)))) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((False ∨ (p2 ∨ False)) → (((p5 → p4) → p5) ∨ ((p3 ∨ p5) ∨ True))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h11 := h4 h5
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : (p3 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h13
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h14 := h11 h12
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h18 =>
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112511403717082263543596241561 : ((((((((((p3 ∨ p5) ∨ p1) → False) ∧ (((p5 ∨ (False ∧ False)) ∧ False) ∨ (p3 ∧ False))) ∨ p1) ∨ False) ∨ True) → p4) → p5) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213208144934281633789603327905 : ((((p2 → False) ∨ p4) ∧ True) ∨ ((((True → (True ∨ p3)) ∨ (p5 → ((p3 → (p5 ∨ p1)) → (p3 ∨ p2)))) → p5) ∨ (True ∧ (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164958023919067360395103712268 : ((((p1 ∨ (((((((p5 ∨ p3) ∨ p1) → p5) ∨ p3) → p2) ∧ True) ∨ p2)) → p2) → p3) ∨ (p3 ∨ (p2 ∨ (False → ((p4 ∧ p1) ∧ False))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774225055429194916938451726680 : (((False ∨ ((p2 ∨ (False ∨ ((False ∨ ((False ∨ (p1 ∨ ((p5 → p5) ∨ ((p3 ∧ p1) ∧ p3)))) ∨ p5)) ∨ False))) ∧ ((p1 ∧ p2) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325077176869283441951475402756 : (p5 ∨ ((p5 ∨ p2) → (p4 → ((((p5 ∧ (((p1 → p3) → True) ∧ True)) → ((p1 → (p1 → p3)) ∧ (True ∧ False))) ∨ p4) ∨ (p5 ∧ p4))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116795986568132098206279914749 : (((p2 ∨ p2) ∨ ((((True ∨ p3) ∨ (((p4 → (False → p3)) ∧ (p5 ∨ p2)) → p2)) → (False ∨ False)) → (p4 ∧ (False ∧ p2)))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111026009103773644543273883398 : (((((True → p1) ∨ (p1 → ((p1 ∧ ((True ∧ True) → ((p3 ∧ (p3 → True)) ∧ p1))) ∨ p2))) → (p1 ∧ (p5 ∧ p2))) ∧ False) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696378935272746866671756089998 : ((((p5 → (((((p3 ∧ (p5 ∧ False)) ∧ (False ∧ p2)) ∨ p5) → p5) ∧ p1)) → (((p4 → p2) → p2) → (((False ∧ False) ∨ p1) → p1))) ∨ p3) ∧ True) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318058192646171657834002269655 : (p4 ∨ ((((p4 ∨ (p5 ∨ (((False → False) → p3) ∨ p2))) ∧ (((((p5 ∧ p1) ∧ p1) → p1) ∧ ((p3 ∨ p4) ∨ p5)) → False)) ∨ False) → p2)) := by
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
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h6 : ((((p5 ∧ p1) ∧ p1) → p1) ∧ ((p3 ∨ p4) ∨ p5)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h7
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h8.left
        let h11 := h8.right
        -- One of the premise coincides with the conclusion.
        exact h9
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h12 := h4 h6
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h15 : ((((p5 ∧ p1) ∧ p1) → p1) ∧ ((p3 ∨ p4) ∨ p5)) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h16
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Conjunctions on the left can always be decomposed.
          let h19 := h17.left
          let h20 := h17.right
          -- One of the premise coincides with the conclusion.
          exact h18
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h21 := h4 h15
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h24 : ((((p5 ∧ p1) ∧ p1) → p1) ∧ ((p3 ∨ p4) ∨ p5)) := by
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Implications on the right can always be decomposed.
            intro h25
            -- Conjunctions on the left can always be decomposed.
            let h26 := h25.left
            let h27 := h25.right
            -- Conjunctions on the left can always be decomposed.
            let h28 := h26.left
            let h29 := h26.right
            -- One of the premise coincides with the conclusion.
            exact h27
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
            have h30 : (False → False) := by
              -- Implications on the right can always be decomposed.
              intro h31
              -- False on the left can always be used.
              apply False.elim h31
            -- We have shown the premise of h23, we can now drive its conclusion.
            let h32 := h23 h30
            -- One of the premise coincides with the conclusion.
            exact h32
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h33 := h4 h24
          -- False on the left can always be used.
          apply False.elim h33
        case inr h34 =>
          -- One of the premise coincides with the conclusion.
          exact h34
  case inr h35 =>
    -- False on the left can always be used.
    apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102784266168849816215039352489 : ((((((p3 ∧ p4) → (p4 ∧ (p5 → ((p2 ∧ p3) → (p4 ∧ p2))))) ∧ ((p4 → (p5 ∧ (p5 ∧ True))) → False)) → p3) ∨ True) ∧ (True ∨ False)) := by
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
theorem thm_5_vars_157929329093351367406728131669 : ((((p1 ∨ (((p5 ∧ p5) → p3) ∧ p5)) ∨ p4) ∧ (((p2 ∧ (p2 ∨ (p5 → p2))) → p4) ∨ p2)) ∨ (True ∨ (p1 → (p5 → (True → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599172473265860021077679538843 : (((((p3 → True) ∧ ((p4 → (((p3 ∧ (False → ((p1 ∨ (p1 → (p2 ∧ (p4 ∧ p1)))) ∧ False))) ∨ (p1 ∨ False)) ∨ p1)) ∨ p1)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308536240226537947124472562870 : (p2 ∨ (((p1 ∨ ((((False → ((p4 ∧ p2) ∨ False)) → p1) ∨ p2) ∨ True)) ∨ (((((p5 → (p2 → p4)) ∨ p1) ∧ p3) ∨ p4) ∧ True)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45352959151861857942261866799 : (((p4 ∧ (((True → (p2 ∨ p3)) ∧ (p2 ∨ (p4 → (p3 ∨ (p3 ∨ (((((p5 ∨ p3) ∨ p1) ∧ p5) ∨ p3) ∧ p1)))))) → p5)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_385968525437882945233725252406 : (((((((((p2 ∨ ((p1 → True) ∨ ((p1 ∧ (p1 ∧ p5)) ∨ False))) → (p1 ∨ (True ∧ p4))) ∨ p3) ∨ True) ∨ p3) ∨ (p2 ∨ p4)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_171705132425617548313204725185 : (((p3 → ((p1 ∧ True) ∧ ((p1 → False) ∧ (False ∨ ((p5 → p1) ∨ p1))))) ∨ p1) ∨ ((p1 ∨ ((p2 ∨ p3) ∨ (p3 ∧ p3))) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68189960176023856051990792359 : ((p3 → (((((False ∧ True) → (((False ∨ p2) → (p2 → p1)) ∧ p5)) → False) ∨ ((p1 ∨ False) → (p3 → (p4 ∧ (p3 → p5))))) ∨ p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198664966792348784246632242654 : ((p4 ∨ (((False → (p1 → False)) → p4) ∧ p5)) ∨ ((p3 → p5) → ((False ∨ p4) → (p3 → ((((p1 ∨ p3) → p3) → p4) → (p3 ∨ True)))))) := by
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
  cases h2
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50170091164845846684711061043 : (((((((False ∧ False) ∧ ((True ∨ p5) ∨ (p4 → p4))) ∨ ((True ∧ False) ∨ (p4 ∨ p3))) ∧ False) ∧ p2) ∨ ((False ∧ p2) ∧ (True ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63913603617235620767726704252 : ((False ∨ ((False ∨ ((p3 ∧ (p4 ∨ (True → ((((p3 ∧ (True → p4)) ∧ p2) → False) ∨ (False ∧ p5))))) → ((True ∨ p3) ∧ p4))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149226996449068794988519057763 : (((p4 ∧ True) ∨ (((True ∧ (False → True)) ∧ ((False → p1) → (p2 ∨ (p3 ∨ (p5 ∧ True))))) ∧ (p4 ∧ p2))) ∨ (False ∨ ((p2 ∧ p3) → p2))) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698442966445178199982773042664 : (((((p1 → (((p3 → p4) ∨ p2) → p2)) ∧ (p3 ∨ (p4 → p5))) ∨ (True ∨ (p4 ∧ ((((p3 ∧ p3) ∧ p4) ∨ True) ∧ (p4 ∧ p1))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_803308478038093825548692832058 : (((p3 → ((((((p5 ∨ (p5 ∨ p2)) → p2) ∧ p2) → p5) → ((((p4 ∨ p3) ∨ (p4 ∧ p5)) ∨ p1) → (False ∧ (p5 ∨ p4)))) ∨ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687687826940518028888929110263 : ((((((((True → True) → p1) ∨ (((p4 ∧ p5) → p5) ∧ p3)) ∧ p2) ∧ (p3 ∨ False)) ∧ ((p2 ∧ (p3 → (p3 → (p5 ∨ True)))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705413222306305012440477316409 : (((((p3 ∧ (((p5 ∨ p5) → p3) ∨ p5)) ∨ False) ∧ ((True ∧ ((p2 ∧ p4) → p5)) ∧ (((p5 ∨ p4) → (False → (p3 ∧ p3))) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_473063814254045630831139560713 : (((((((p1 → ((p5 ∧ p4) ∧ (p2 ∨ False))) ∧ False) → False) → p2) → (((p3 ∧ (p5 ∨ p2)) → (((p3 ∨ p3) ∨ True) → p2)) ∨ p5)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 → ((p5 ∧ p4) ∧ (p2 ∨ False))) ∧ False) → False) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h7.left
      let h12 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h7.left
      let h17 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h19 =>
        -- One of the premise coincides with the conclusion.
        exact h19
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h7.left
    let h22 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h24 =>
      -- One of the premise coincides with the conclusion.
      exact h24
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84003219552570785098470009197 : ((((((p2 ∨ (p2 → False)) ∧ True) → (((p1 → (p1 → p2)) → p5) → True)) ∨ p2) ∧ (True → (((p2 ∧ p3) ∧ (p1 → p4)) ∧ p4))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300643391104137787019770184561 : (False ∨ (((((False → p4) → (p4 ∨ p4)) → p2) ∨ (((p4 ∧ True) → ((p2 ∨ True) ∨ p2)) ∨ p2)) ∧ (p5 → (((True ∧ p2) → False) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313020066257728194748866481201 : (p3 ∨ (((p3 ∧ (((p5 ∧ (((p2 ∨ True) → (p3 ∧ p3)) → ((p1 ∨ (False ∧ p4)) ∧ ((p1 ∧ False) → True)))) ∨ p2) ∧ p2)) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205973148166618774293842682178 : ((p1 ∧ ((p3 → (p4 ∨ p1)) ∨ False)) ∨ (p1 ∨ ((p4 → True) ∨ (False ∨ (((p4 ∨ (True ∧ (p5 ∧ (p2 ∨ p1)))) ∨ (p5 → p3)) → True))))) := by
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
theorem thm_5_vars_673797492506000552506511396583 : (((((True ∨ p4) ∨ (p3 ∧ ((True ∨ p5) → (((p5 → (p4 → False)) ∨ (p3 ∧ ((True → False) ∨ p3))) ∧ p5)))) → (p5 ∧ (True ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263440226860128163790055122744 : (True ∧ ((((p5 ∨ ((True → p4) ∧ (p1 ∧ (((p1 ∨ (False ∧ p1)) ∨ ((p1 ∧ False) → p2)) → True)))) ∧ True) ∨ False) → ((False ∨ p5) ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h12 := h7 h11
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322422765403427081380680692817 : (p5 ∨ (((((p1 ∧ p4) → p3) → ((p3 ∨ False) → p4)) ∨ (((True ∨ False) ∨ ((p3 ∧ False) ∨ ((p5 ∨ p4) ∧ p4))) ∨ (p2 ∧ p1))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214497132966543872187406999903 : (((p2 ∧ p3) ∧ (p4 → p1)) ∨ ((p4 ∨ (((p1 → p4) → ((p3 → (False ∨ (p2 ∧ True))) → False)) ∨ (True ∧ ((True ∧ False) → p3)))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248713073115419178294610610210 : ((p3 ∨ p2) ∨ (((p4 ∨ p5) ∨ p3) ∨ (p1 ∨ (((((True → p1) ∧ ((p3 ∧ False) ∧ (p5 → True))) ∧ (p5 ∧ p1)) → p2) ∨ (False ∧ True))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h9



