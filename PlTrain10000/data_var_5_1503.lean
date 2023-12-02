variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39337580249941556996293212136 : (((p2 ∧ ((p4 ∧ (False → p2)) ∨ ((p1 ∧ (True → p1)) ∨ (p4 ∨ ((p4 → False) ∧ (((p3 → (p2 ∧ p5)) → p2) ∧ p3)))))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137268836037619518590385686393 : ((p1 ∧ (p1 ∨ (((p2 ∨ (((p1 → ((True ∨ ((False ∧ p1) ∨ p5)) ∨ False)) ∧ p3) ∨ p5)) → p5) ∧ (False ∨ p4)))) ∨ (False ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117617439056308182415452311777 : ((p3 ∧ (((True ∧ ((True ∧ ((False → p2) ∧ ((p5 → (((p3 ∨ (p4 ∨ p4)) ∧ True) → p4)) → p5))) ∨ p3)) ∨ p2) ∧ p3)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149977704204919044062290398044 : ((p4 ∨ ((((p4 → True) ∧ False) ∨ p1) ∧ (p5 ∧ ((True ∧ (p5 ∧ p2)) ∨ (p2 ∨ ((p1 ∧ p2) → p4)))))) ∨ (p4 → (p3 → (True ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190500203343146311850934985629 : (((((p3 → p2) ∨ ((p4 ∧ p1) → True)) ∨ p1) → p3) ∨ ((True → (True ∧ (False → (((p4 → p3) → p4) ∧ (p4 → (p1 → p3)))))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608204699435897805782867797709 : ((((((p5 ∨ ((((((False → p3) ∨ p5) → p5) ∧ p3) ∨ ((p3 → (False → False)) ∧ (p3 → (p2 ∨ True)))) ∧ False)) ∧ p2) ∨ True) ∨ p1) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_809332121090616307288215307602 : (((p5 → ((p4 ∧ (((p3 → ((p2 → (((p5 ∨ p1) ∨ p3) ∨ (p2 ∨ False))) → (p4 ∧ p5))) ∧ p4) ∧ (p1 ∨ (False → p2)))) ∨ p5)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305493631904704484540532536887 : (p1 ∨ (((((p2 ∧ (p4 → (p3 → (p3 ∧ False)))) ∨ p2) ∧ (False ∨ p2)) → False) ∨ (((False ∧ (p4 ∨ p1)) ∧ (True → p4)) → (False → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302635069315384411232879941533 : (False ∨ (p2 ∨ ((p1 ∧ (p4 ∧ (((p5 ∨ (p5 ∧ ((p3 → (True ∧ True)) → (p3 ∧ p4)))) ∧ p2) → (p3 → p4)))) → ((p2 → False) ∨ p4)))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103319806584466046924631596152 : (((p3 ∨ (p1 ∧ ((((p1 → True) ∨ True) ∧ (((p4 → True) ∨ (True → (p3 → ((p1 ∨ p3) ∨ p4)))) ∨ p1)) → p2))) ∨ True) ∧ (False → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51696003927645651810532067303 : (((((p5 ∧ ((p4 ∨ (p2 → False)) ∨ p5)) ∧ (p1 → p2)) ∧ ((p3 → p5) ∨ True)) ∧ (p2 → (p1 ∧ ((False ∧ p1) ∧ (p5 ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327741819689995912144030797339 : (True → ((((p5 ∧ False) ∧ p5) ∨ (((False ∧ (p4 ∨ (p3 ∨ ((p1 ∧ (p4 ∧ False)) ∧ p1)))) ∨ ((p3 ∧ p5) → p5)) ∨ p3)) ∧ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183882417923436606741954279489 : ((((p4 ∨ (p3 ∨ p2)) ∨ ((p4 ∧ (p3 → p3)) ∨ False)) ∧ False) ∨ (((((p1 → p2) → p2) ∨ p3) → (p2 → p2)) ∧ (p4 → (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788973829893778737633081861169 : (((p5 ∨ ((p5 ∧ ((p3 → ((False → ((((p4 ∧ p5) → p4) ∨ (p2 ∧ ((False ∨ True) ∨ p4))) ∨ p4)) → p4)) → p4)) ∨ (p3 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40482594823706589465860515294 : (((((p3 ∧ p2) ∨ (((((True ∨ p5) → (((((p4 → (p4 → False)) ∧ p2) → p1) → p1) ∨ p1)) ∨ True) ∧ p5) ∨ True)) ∨ p4) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59478528929723619730551052740 : (((p1 → p2) ∨ (p5 ∨ (False ∧ ((((p4 ∨ (False ∧ ((p2 ∨ ((p5 ∨ p1) ∧ p3)) ∨ True))) ∧ p2) ∧ (p3 ∧ p3)) ∨ (p5 → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174416257994415326842174538491 : ((((True ∧ (False ∨ p1)) ∨ ((p3 ∨ p1) ∨ False)) ∨ (p2 → ((p3 → True) ∨ p1))) → (p2 ∨ ((((p2 → p2) ∧ p4) ∨ False) ∨ (p4 ∨ True)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
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
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53220252134633616511078459152 : ((((p1 → (((p4 ∧ p3) ∧ p1) ∨ p5)) → (p4 ∨ (True → False))) ∨ ((p3 → (True → (p5 ∨ (True ∨ p2)))) ∨ ((False → p3) ∨ False))) ∨ p5) := by
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
theorem thm_5_vars_318617869562237764555541400294 : (p4 ∨ (((p2 ∧ p5) ∧ (False ∧ ((p3 ∧ p4) → (p1 ∨ (p1 ∧ ((True ∨ True) ∧ (p5 ∧ ((p5 ∨ (p4 ∧ True)) → True)))))))) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113786676356125216087456640368 : ((((p1 ∧ p3) ∧ (((p3 ∨ p4) → p2) → ((((False ∨ (False → True)) ∧ p2) → (True ∨ p1)) → (p2 ∧ p2)))) → (False ∧ p1)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67415520255259297449561227137 : ((p1 → ((((p4 ∧ ((((p5 → True) → p2) ∧ False) ∧ p4)) ∨ (p1 → (p5 ∧ False))) ∨ (((p5 ∧ True) ∧ p4) ∨ p1)) ∨ (False ∨ False))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158202005710102143147451117269 : ((((p3 ∧ p4) ∨ p3) ∧ (p1 ∨ ((True ∧ (((p5 → False) ∧ p3) ∧ (p3 ∨ (p5 ∧ p4)))) ∧ False))) ∨ (False → (((True ∧ p1) → p2) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184142048508763010376782553355 : (((p5 ∧ ((p5 → False) ∧ ((p5 ∨ (p4 ∧ p5)) ∧ p4))) ∨ p5) ∨ (((((True ∧ p3) → p5) ∧ (p2 ∨ p5)) → (True ∨ True)) ∨ (p4 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351269804330072079196737825250 : (p4 → ((p4 → (((True → (p3 → p5)) → (((((True → p2) ∧ p1) → (p4 ∧ (p2 ∨ p3))) ∧ p3) → p3)) → False)) ∨ (False → (p3 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329699556939153798831993050709 : (True → ((p5 ∨ p2) → (((p3 ∧ ((p5 → True) ∨ p5)) ∨ ((((False ∧ p4) ∧ True) → False) ∧ (p4 ∧ ((p1 ∧ (False → False)) ∨ p3)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_588660147854647011069775799615 : (((((p1 ∧ (((p1 ∨ (p3 ∨ p1)) → ((((p4 ∨ ((False → p1) → (p4 ∧ p4))) ∧ p4) ∧ True) → (p5 ∧ True))) → False)) ∨ p3) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792257250042174451667511462454 : (((True → (((p5 → p4) → (False ∧ (((((p1 ∧ ((p3 ∨ p1) ∧ p4)) ∨ p3) → p2) ∨ p4) → p5))) → (p2 ∨ (True → (p2 ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588321440726144214599223002485 : ((((((((p1 ∧ p5) → False) ∧ p5) ∨ ((((((p2 ∧ (p5 ∧ p5)) ∧ p4) → ((False ∧ p5) ∧ False)) ∧ True) ∨ p4) → p2)) ∨ p2) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305582411026963732049377540285 : (p1 ∨ (((((p2 ∨ ((p4 ∨ p4) → p2)) → (p4 ∧ p5)) ∨ False) → p1) ∨ ((((p1 ∨ (p4 ∧ p3)) → ((p4 → False) ∧ p2)) ∧ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335817326046672070669634164321 : (p1 → (((((p2 → False) ∨ p2) ∨ (p3 → ((p1 ∧ True) → ((False ∨ (p4 ∧ (False ∨ p2))) ∨ p3)))) ∨ (((p1 → False) ∧ p1) ∧ p5)) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674751404601332607198478155628 : ((((p3 → (((False ∧ False) → True) → (((p5 → ((p5 → (p3 ∨ False)) ∧ ((p4 ∨ True) ∧ True))) → True) ∧ p5))) → ((p4 ∨ p3) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77133666735776252959116604185 : ((((True ∧ (p4 ∨ (p3 ∨ p1))) → (p2 ∨ (((False → (p3 ∨ (p1 ∨ p3))) → (p4 ∧ (p3 → (p4 ∧ True)))) → (p3 → p4)))) → False) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∧ (p4 ∨ (p3 ∨ p1))) → (p2 ∨ (((False → (p3 ∨ (p1 ∨ p3))) → (p4 ∧ (p3 → (p4 ∧ True)))) → (p3 → p4)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h13 : (False → (p3 ∨ (p1 ∨ p3))) := by
          -- Implications on the right can always be decomposed.
          intro h14
          -- False on the left can always be used.
          apply False.elim h14
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h15 := h11 h13
        -- We need to get the left conjuct of h15 based on <expert-advice>.
        let h16 := h15.left
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Implications on the right can always be decomposed.
        intro h19
        -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
        have h20 : (False → (p3 ∨ (p1 ∨ p3))) := by
          -- Implications on the right can always be decomposed.
          intro h21
          -- False on the left can always be used.
          apply False.elim h21
        -- We have shown the premise of h18, we can now drive its conclusion.
        let h22 := h18 h20
        -- We need to get the left conjuct of h22 based on <expert-advice>.
        let h23 := h22.left
        -- One of the premise coincides with the conclusion.
        exact h23
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h24 := h1 h2
  -- False on the left can always be used.
  apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335829448859749926726220160412 : (p1 → ((((False ∨ p3) ∧ ((True ∧ (p2 ∨ p4)) → (p5 → ((p4 → False) → (p3 ∧ p3))))) ∨ ((p4 ∧ (p2 ∨ (p2 → p1))) → p4)) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114038813042042916151945588089 : (((((p5 ∧ (((True → ((p1 ∧ (p2 → p4)) ∨ p1)) → False) → (p3 ∧ False))) ∨ p5) ∧ (p1 ∨ p5)) ∨ ((True ∨ p2) ∧ True)) ∨ (p4 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_709826492256114691529656748485 : ((((p3 → (p1 ∨ (p4 → ((p1 → p5) → p4)))) → (((p2 → (p4 ∨ p4)) → ((p2 ∧ ((p2 → p2) ∧ (p4 ∧ p5))) ∨ p1)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_404618990930570163716281441415 : ((((((True → (p1 → ((False → (False ∧ (p3 ∨ (True ∧ p2)))) → (p2 ∨ ((p5 ∨ (p4 ∧ (True ∧ p2))) ∧ p3))))) ∨ True) → p5) → p5) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True → (p1 → ((False → (False ∧ (p3 ∨ (True ∧ p2)))) → (p2 ∨ ((p5 ∨ (p4 ∧ (True ∧ p2))) ∧ p3))))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186021648600401504187171044048 : (((p4 → (p3 ∧ (True ∨ (p2 ∨ (False → (p3 ∨ p2)))))) ∧ p1) → ((((p5 → False) ∧ p3) ∧ ((True ∧ False) → (p5 ∧ (p1 ∨ p5)))) → p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227937401615189828613996956466 : ((p3 ∧ (p1 ∧ p3)) ∨ ((p4 → (p3 ∧ (((p3 ∧ (p4 ∨ (((p3 → False) → False) ∧ False))) ∧ ((p1 ∨ p5) ∧ p5)) ∧ (True → p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135675537064500138890202716493 : (((p3 → ((((p3 ∧ (p1 → (((False ∧ False) ∧ p2) → p4))) ∧ p3) ∧ True) → p5)) → (p4 ∨ ((p3 ∨ p3) ∧ False))) ∨ ((False → p5) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746869824847342166650542855027 : ((((p4 ∨ True) → ((p5 → True) ∧ (((p1 → (p4 ∨ False)) → ((p1 ∨ p4) → ((p5 ∧ True) → (((False ∧ p2) ∨ False) ∧ p3)))) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238280639344653221123807018234 : ((True ∨ p5) ∧ (False ∨ (((p3 ∧ (True → (p5 ∨ (p1 ∧ p5)))) ∨ ((False → p4) → p2)) ∨ ((True ∨ ((p1 ∧ (p5 ∨ p5)) ∧ False)) ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_44328807561000496560882453605 : ((((p1 → (p4 → (False ∨ ((((True ∧ (p1 ∧ p5)) ∧ p3) → (p4 ∨ False)) ∧ p1)))) ∨ ((((p4 ∨ p3) ∧ False) ∧ p2) → p4)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1817481750598543100591368088 : ((True → ((((p5 ∧ False) → ((p2 ∨ False) → (True ∨ ((True → p3) ∨ p1)))) → p3) ∧ ((p1 ∧ p2) ∧ p5))) ∨ ((True ∨ p3) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254171329181575623417956710736 : ((p2 ∧ p1) → (((p4 → (p3 ∨ p4)) ∨ (((p3 ∧ (True → p1)) → True) → p1)) → (True ∧ ((p4 ∨ ((p4 ∧ p5) ∨ p1)) ∨ (p4 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789727079145055867535253966516 : (((p5 ∨ ((p3 ∨ ((True ∧ p5) → p4)) ∧ (p5 ∧ (((p2 ∨ (p2 ∧ ((p5 ∧ (p5 → p2)) ∨ p1))) → (False ∧ p2)) ∨ (p2 ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611866390396628172764268027263 : (((((p4 → ((False ∧ p1) ∧ ((p3 → ((False ∧ p4) → ((True → (False ∨ (p5 → p5))) → p4))) → (p3 → (False → p5))))) → False) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_151331642048435065347034361834 : (((p1 → (((p5 → ((((p3 → (p1 → False)) ∨ p1) → p4) → p4)) ∨ ((True ∨ p3) ∨ p3)) ∧ True)) → p5) → (p1 → ((p4 ∨ p3) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : (p1 → (((p5 → ((((p3 → (p1 → False)) ∨ p1) → p4) → p4)) ∨ ((True ∨ p3) ∨ p3)) ∧ True)) := by
      -- Implications on the right can always be decomposed.
      intro h6
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
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h5
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : (p1 → (((p5 → ((((p3 → (p1 → False)) ∨ p1) → p4) → p4)) ∨ ((True ∨ p3) ∨ p3)) ∧ True)) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h9
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_426315735398629099458109151701 : ((((p3 ∨ ((p5 ∨ False) → ((p3 ∨ (((p3 → (p4 ∧ p5)) ∨ (True ∧ (p2 ∧ p4))) ∧ (p2 ∧ (p1 → p2)))) ∨ True))) ∧ (p4 ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157995422474005587061341387975 : ((((p1 ∨ p1) ∨ (((True ∧ p4) → p1) → False)) → ((p5 ∧ (False ∨ ((p2 ∨ p1) → p1))) ∧ p5)) ∨ (p5 ∨ (p1 → (p4 ∨ (p1 ∨ p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610826900228690095401350734429 : (((((((p5 ∧ p3) ∨ (True → ((p4 → True) → (p5 ∧ ((p2 → p2) ∧ p1))))) ∧ ((True ∧ p3) ∧ (p5 → (p5 ∨ False)))) → p2) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_300061356974927909575646379620 : (False ∨ ((((p4 ∨ ((p3 ∨ p3) ∧ (p4 ∨ ((p2 ∨ ((p5 ∧ (p4 → p5)) ∨ (p2 ∨ p4))) → (p3 ∨ p3))))) ∧ False) ∨ False) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60019493368506378308502277322 : (((p1 ∨ p1) → ((((((p1 ∨ p3) → (p5 ∨ p4)) ∨ True) ∨ ((p4 ∨ p3) ∨ (True ∧ (((p2 ∧ p5) → p5) ∨ False)))) ∨ p4) ∨ p2)) ∨ False) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212254239018696778706430509629 : ((False ∨ (False ∨ (False ∨ True))) ∧ ((((True → (p2 → ((p2 ∧ True) ∧ p5))) ∧ ((True ∨ (True ∨ True)) ∧ p3)) ∨ p1) ∨ (True ∨ (False → p5)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114941353156133256486392130376 : ((((p4 ∨ (False ∨ p2)) ∧ (((p4 → ((p2 → p4) → p2)) → p3) ∧ p3)) → (p1 ∧ (p5 → ((p3 ∨ (p2 ∨ p1)) → p2)))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177980030945401684438674862389 : (((p1 ∧ (p3 → (p4 ∧ ((p2 ∧ True) → ((False ∨ p2) ∧ p3))))) ∨ p4) ∨ (((p4 ∧ (p5 ∨ p2)) ∧ p5) ∨ (p1 ∨ (p3 ∨ (False ∨ True))))) := by
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
theorem thm_5_vars_323897086718784308191778463131 : (p5 ∨ (((((p4 → ((p4 ∧ p3) → (True → True))) ∧ p1) → p2) ∨ ((p2 → p1) ∧ False)) ∨ ((((p5 ∨ False) ∧ (p2 ∨ p5)) ∧ False) → p4))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h3
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254329287572470566498117841283 : ((p2 ∧ p4) → (((((p2 ∧ p5) ∨ p2) → (((False ∨ p4) → p3) ∧ (((p2 → p5) → p3) ∨ ((p1 ∧ p1) ∧ (p5 ∧ p5))))) ∧ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263682731525844520847823047455 : (True ∧ ((((((p1 ∧ p5) ∧ True) → p5) → (p2 ∧ ((p5 ∨ ((False → p3) ∨ p4)) ∨ p3))) ∨ p4) ∨ ((((p1 ∨ p3) → p1) ∨ p2) ∨ True))) := by
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
theorem thm_5_vars_201239203868448925566259439019 : ((p2 → (p1 → ((p2 ∧ (p1 ∨ p3)) ∨ p3))) → (p3 → (p4 → ((((p5 → (p1 → p2)) ∨ p5) ∧ (p5 ∨ ((True → p3) ∧ True))) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165616047823041589076762454884 : (((p1 → (p2 ∧ ((False → (p2 ∨ p5)) ∧ p3))) → ((p4 ∨ (p3 ∧ (p1 → p5))) ∨ p1)) ∨ (False → (p4 → ((p1 → False) ∨ (p1 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740904035943407385256220285755 : ((((p3 ∨ p2) ∨ ((((((((((p5 → (p4 → p4)) ∨ p2) → p5) ∨ p1) → (True → p4)) → p1) ∨ (p4 ∨ False)) ∨ False) ∨ p2) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336369902719268338323635057023 : (p1 → (((p1 → True) → ((False ∧ ((p2 ∧ (p1 ∨ (((p4 → p2) ∨ False) ∨ ((p3 ∧ (p3 ∨ p5)) ∧ (p2 → p2))))) → p3)) ∨ False)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113688290849114641133167672705 : (((((p3 → (((p1 → (((True → p4) ∨ (p3 ∧ p5)) ∨ (p5 → p1))) → (p2 ∨ p4)) ∨ p3)) → p4) → False) → (p5 ∧ False)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671281267794650535932266983486 : ((((p5 ∨ (((((p2 → p3) → (True ∨ p2)) → ((True → (False ∧ p4)) ∧ p4)) ∧ (p2 → p5)) → (p1 → False))) ∨ ((True ∧ p3) → p3)) ∨ p5) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112077842485329763376050506536 : ((((p2 ∧ p3) ∨ (p4 → ((p1 ∨ (False ∨ ((((p3 ∧ p3) ∧ (p2 → p3)) → True) ∧ ((p3 → False) → True)))) ∧ False))) ∨ True) ∨ (p5 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196669196448327257183575993201 : ((((p1 ∨ ((p2 ∨ False) → p1)) ∧ True) ∧ False) ∨ (p2 → (True → (p3 → ((p1 ∧ p4) ∨ (p4 ∨ (True ∨ (p1 ∧ (p3 ∨ (p2 ∧ p2)))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664922136949395970565309719281 : ((((p3 → (((p3 ∨ p2) ∧ (p3 ∧ (((p5 ∨ False) → (p5 ∨ True)) ∧ (True → ((p5 ∨ p3) ∨ (False ∧ p3)))))) → p1)) → (p1 → p1)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148977451329203460217082964555 : (((False ∧ (p3 ∧ p4)) ∧ ((p2 ∧ p2) ∨ ((p2 → ((False ∨ (False ∨ True)) ∨ (False ∧ p1))) → (p5 → True)))) ∨ (p4 ∨ ((True → p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2378438377707492208062123602 : (((False → p1) → (p5 ∧ ((((p2 → p2) ∨ p2) → p4) → False))) ∨ (((True ∧ False) ∧ ((p1 → ((p1 ∧ p2) ∨ p4)) ∨ p2)) → p5)) := by
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
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312473306616408950206285388282 : (p2 ∨ (p5 → (((False ∧ ((p5 ∨ p1) ∧ p3)) ∨ (((True → (((p5 → ((p1 → p5) → p5)) ∨ True) ∨ (True ∨ p3))) → p3) ∧ False)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126465394200153226145559983748 : ((p2 ∧ ((((((((p4 ∨ p5) ∨ p1) ∨ False) ∧ p3) ∨ (p4 ∧ p3)) ∨ (p5 ∨ False)) → (False ∨ (False → True))) → (p1 ∨ p4))) → (p1 ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((((((p4 ∨ p5) ∨ p1) ∨ False) ∧ p3) ∨ (p4 ∧ p3)) ∨ (p5 ∨ False)) → (False ∨ (False → True))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
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
        case inr h18 =>
          -- False on the left can always be used.
          apply False.elim h18
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h22
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h25
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h26 =>
        -- False on the left can always be used.
        apply False.elim h26
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h27 := h3 h4
  -- Disjunctions on the left can always be decomposed.
  cases h27
  case inl h28 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h28
  case inr h29 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55053558825266389047333067083 : (((False ∨ (p4 → ((False → p5) ∨ p5))) ∧ ((True ∨ p5) ∧ ((p4 ∨ False) → ((p3 ∨ ((p3 ∨ p5) ∧ (False ∧ (p1 ∧ p2)))) ∨ p4)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345489331984045427857118519149 : (p3 → (((p3 ∧ (False ∨ (True → ((p3 ∧ (False ∨ ((((p2 ∧ True) → True) → p2) ∧ p3))) ∨ p1)))) ∨ (((False ∨ p3) ∨ p3) → p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612520104234601233781925835615 : (((((((p3 → (p3 ∨ ((p4 ∧ p1) ∧ p1))) → ((p5 ∨ p2) ∨ ((((p5 ∨ p1) → False) ∨ p4) → p4))) ∨ p5) ∨ (p5 ∨ True)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_737182555956454076039358614421 : ((((p3 → p5) ∧ (((p3 ∧ (True ∨ p1)) ∨ (p5 → p2)) → (p5 ∨ ((p3 ∨ ((p4 ∨ ((p1 → (False ∨ p3)) → p3)) ∧ p4)) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165583268108802110756703917690 : (((p3 ∧ ((p3 → False) ∧ (p1 ∨ (p4 ∧ True)))) ∨ (p1 ∨ (((True ∧ p3) → True) ∨ p5))) ∨ ((p2 ∧ p5) → (((True ∨ p4) → p3) ∧ True))) := by
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
theorem thm_5_vars_342804112816780311222214863275 : (p2 → ((p1 → (False → ((p1 ∧ (p4 ∨ p5)) → p5))) → (p2 ∧ (((p3 ∧ ((((p4 → p4) → p2) → (p1 ∨ p1)) ∧ p2)) → p1) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : ((p4 → p4) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h10 := h6 h8
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148316178655309229878603373011 : (((p1 ∨ (p3 ∨ ((p5 ∧ False) ∧ ((p2 → p1) ∧ (p3 ∧ (p1 → (p1 ∧ False))))))) → (p3 ∧ (p4 ∨ p2))) ∨ (((p3 ∧ p5) → p5) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40581083163136132131408210113 : ((((((((p5 ∧ (p2 ∨ p5)) ∨ True) ∨ ((p1 ∨ ((p5 ∧ (p5 → p4)) ∧ p2)) ∨ (p3 → p4))) ∨ (p3 → p5)) ∧ p3) → p2) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682813443443480070685199771360 : ((((((False ∨ p3) ∨ p4) ∨ ((((p2 → (p5 → p2)) → p2) → ((p1 ∧ False) → p5)) ∧ p4)) ∧ ((p4 ∧ True) ∨ (p2 ∧ (False → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50861178049862253807286252196 : (((((p5 → (p1 ∧ (p4 → (p3 ∨ True)))) → ((False → (p4 ∨ (p1 ∧ p2))) → p3)) ∨ p2) ∧ (p4 → (p1 → (p4 ∧ (p4 ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152427453813827335195940697816 : ((((p1 → True) ∧ p4) ∧ (False ∨ (p5 ∧ (p2 ∨ (p5 ∨ ((p5 → (p5 ∨ p1)) ∧ ((False → p3) → False))))))) → ((p3 ∧ p4) ∨ (p3 ∨ p5))) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593003928167259708329669864376 : ((((((((True ∧ p3) ∨ (p4 ∨ ((True ∨ p4) ∨ (p1 → (p3 ∨ ((True ∨ True) ∧ p4)))))) → False) ∧ p3) ∨ ((False ∧ p2) ∨ True)) ∧ True) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149549653671349787762707457516 : ((p2 ∧ ((((p3 → (((p2 → p4) → (p5 ∨ p3)) ∧ (p5 → p4))) ∧ p5) ∨ p2) ∨ ((p4 → p2) ∧ True))) ∨ (p1 ∨ ((p3 → p3) ∨ p5))) := by
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
theorem thm_5_vars_308592207207839800366779174965 : (p2 ∨ (((p1 ∧ (p4 ∨ p1)) ∨ ((p2 ∨ p5) → ((p2 ∨ (p1 ∨ p4)) ∧ ((p1 → ((False ∨ True) ∨ (False ∧ (p4 → p3)))) → p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776574370345410331325821051498 : (((p1 ∨ (((True ∨ p1) → ((p4 → (((False ∧ p5) ∨ p4) ∧ (((p2 ∧ p3) ∧ (False ∨ (True ∨ p1))) ∧ (p1 ∨ True)))) ∧ p1)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180929633346151229063647829151 : (((p3 ∧ p1) ∧ (((p4 ∨ ((p2 ∧ p3) ∨ p5)) → (True ∨ True)) ∧ p4)) → ((p2 → (((False ∧ False) ∨ False) ∧ ((p5 → False) → True))) ∨ p4)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66188309139924428158298226854 : ((p5 ∨ ((True ∧ (((p1 ∧ (False → ((p5 → False) → (True → p2)))) → (p2 → p1)) ∨ (p4 → p4))) → (((False ∨ p5) ∨ p1) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685339803655717108251153078852 : ((((p4 → ((p1 ∧ (((p5 ∨ (((p3 ∧ (p3 → p4)) ∨ p5) ∨ False)) → False) ∨ p4)) ∨ False)) ∨ (((False ∧ (p4 ∧ p2)) ∧ p3) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594697355878853600198663635364 : ((((((((p2 ∧ ((p5 ∧ True) → p3)) ∧ p4) → p1) → ((True ∧ False) ∨ (p5 → p4))) → (((p3 → (p1 ∨ p3)) ∨ True) ∧ True)) ∧ True) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141169172631716119276388762900 : (((p1 → (p2 ∨ (p1 ∨ (p2 → p5)))) ∧ ((((((False ∨ p3) ∨ p2) → p1) ∨ (False → p2)) → p4) → (p1 → p1))) → ((False ∨ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68866658417260302114581392509 : ((p4 → (True ∧ ((True ∨ ((((True ∨ p2) ∧ (False ∧ (p2 ∨ (False ∨ p1)))) ∨ True) → p3)) → (True → (p5 → (p2 ∧ (True → p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146918886094908696683689925528 : ((((((p3 ∨ p4) ∨ False) ∧ ((p5 ∨ (p3 ∧ ((False → False) → p5))) → (p4 → (p2 ∧ False)))) ∧ p5) ∧ p1) ∨ (p2 ∨ (p4 → (p4 → True)))) := by
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
theorem thm_5_vars_62713000148716043683007146780 : ((p4 ∧ ((True ∧ (p3 ∧ (((False ∧ p4) ∨ ((p4 → (p5 ∨ p3)) → True)) ∧ (False ∨ ((((p4 ∨ p2) ∧ p2) → p1) ∨ False))))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344399059580892529278320881892 : (p2 → (p4 ∨ (p4 → (((True ∧ (p2 ∧ ((((True → ((True ∨ p3) → p3)) → p1) ∨ ((p2 ∧ p4) → p1)) → p3))) ∨ (p1 → True)) ∧ True)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780011490545141008183629868639 : (((p2 ∨ (((((p3 ∧ p5) → ((False ∨ (p2 ∧ p3)) → ((p1 → p2) ∧ False))) ∨ ((p4 → p1) ∨ p4)) → (p2 ∧ p5)) ∨ (False → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799836384405241787947971004881 : (((p1 → (p4 → (((((False → p4) ∧ p3) ∧ (p2 ∨ ((((p4 → p5) ∨ p3) ∧ ((False ∧ True) → (False ∨ p3))) → p4))) ∧ p5) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725586824636344091644792580277 : (((((p2 ∧ p5) ∧ p5) ∨ ((((False → (((True ∧ p5) ∧ True) ∨ (((True ∧ p4) ∨ (False ∨ p3)) ∨ p2))) ∨ False) → False) → (p2 ∧ p3))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False → (((True ∧ p5) ∧ True) ∨ (((True ∧ p4) ∨ (False ∨ p3)) ∨ p2))) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : ((False → (((True ∧ p5) ∧ True) ∨ (((True ∧ p4) ∨ (False ∨ p3)) ∨ p2))) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341742865757558405480366657882 : (p2 → ((True ∧ ((True ∧ p3) ∧ ((p2 → ((True ∨ p4) ∧ (((p3 → (p4 ∧ (p3 → (p3 ∨ p2)))) ∨ True) → p3))) ∧ p3))) ∨ (True ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112596263121872541786873392294 : ((((True ∧ ((p2 ∨ p4) ∨ (p3 ∧ (p2 → ((p4 → ((False → (p5 ∧ p1)) ∧ p1)) ∧ (False ∨ p2)))))) ∧ (p1 ∨ p3)) → p4) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



