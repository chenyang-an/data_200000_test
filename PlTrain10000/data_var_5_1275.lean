variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179058756394632050025960912153 : ((True ∧ ((((p4 ∨ (((p3 → p5) ∧ p5) ∧ p5)) → p3) → p4) ∧ p4)) ∨ (p2 ∨ ((p5 → (False ∧ (((p3 ∨ True) ∨ True) ∧ p5))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180227002050730545297093715965 : (((False ∧ (((((p1 → p2) → True) → (True ∨ p1)) ∧ p3) ∨ p2)) → p1) → ((p3 ∧ (p2 → p5)) ∨ ((False ∧ p3) → ((False → p5) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113323723858194284763189815763 : ((((p1 ∧ p2) ∧ ((True ∧ (p2 → (p1 ∧ ((p2 → (p4 ∨ p5)) → (True ∨ ((p1 → False) ∨ False)))))) → p1)) ∧ (True ∨ p4)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37338533314476192424351168926 : ((((((True ∧ p2) ∨ ((((p5 → ((True ∧ (p5 → p4)) ∧ p2)) ∨ p1) → ((p1 ∧ (p5 ∨ p4)) ∧ False)) ∧ p5)) ∧ p4) ∨ True) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305286554771196170252716848376 : (p1 ∨ (((((True ∨ (p5 → p4)) → p3) → ((True ∧ p1) ∧ (p3 → (p4 → (True → p5))))) ∧ True) ∨ (p2 → (p2 ∨ ((p1 → p4) → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304724621960430540553690694703 : (p1 ∨ ((((p5 → ((p2 ∨ p5) → p1)) ∧ (p2 → (((True ∧ p4) ∧ p5) ∨ p4))) ∧ (((p4 ∨ p3) ∧ p2) ∧ (True ∨ p4))) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48662119589541949531410777169 : ((((p3 ∧ (p2 ∧ (p3 ∨ (p3 → ((p2 ∨ p1) ∨ (p5 ∧ p5)))))) ∧ (p4 ∨ ((p5 ∧ (p2 ∧ p5)) ∧ p2))) ∧ (p1 ∧ (p3 → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231137980573228076091875119017 : (((p1 ∨ p3) ∨ p4) → ((((p5 ∧ p3) → p2) ∨ ((False ∨ (p4 ∨ (p2 ∧ p2))) → (p1 ∧ p4))) → ((p3 ∨ (False ∨ (False → p3))) ∨ False))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h6
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146346803645972259903142281383 : ((p1 ∨ (((((p1 ∨ (p1 ∧ p4)) → p4) → (p5 ∧ p3)) ∨ (p3 → ((p1 → (False ∨ p1)) ∨ p2))) ∨ False)) ∧ (((p4 → p1) ∧ p3) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134834383117977539066029248426 : (((p2 ∨ ((p3 → p1) ∨ (p5 ∧ (p1 → ((p4 ∧ ((True → (p1 ∧ p3)) → (True ∨ True))) ∨ (False → p2)))))) → p2) ∨ ((p3 ∧ True) → p3)) := by
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
theorem thm_5_vars_714728636002631380848162065264 : ((((True ∧ ((p3 ∧ (p3 ∧ True)) ∨ False)) → ((p4 ∨ p2) ∨ (((p5 → p3) ∧ ((p3 ∧ (p2 → p1)) → False)) ∨ (False ∨ (False → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135564516498037059807169606045 : (((True → ((((p4 ∧ p4) ∨ (p1 → True)) → False) ∨ ((True ∧ p4) → (p1 ∨ p1)))) ∧ (((p5 → p4) ∨ p3) ∧ p5)) ∨ (p3 → (False ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669520539963144329126988570907 : ((((((p2 ∨ p2) ∧ ((True ∧ (False ∧ (p4 → ((True ∧ (True ∨ p4)) ∧ (True ∨ p3))))) ∨ p1)) → (p4 ∧ False)) ∨ (p4 ∨ (True → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758867837174974430476443226146 : (((p2 ∧ ((((((True → p4) ∨ False) → True) ∨ ((p1 ∧ (False ∧ ((p4 → True) ∧ (p3 ∧ p2)))) ∧ (p5 ∧ (p1 → p1)))) → p1) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178341666485384359905530380999 : ((((p3 ∨ p3) ∨ (p2 ∧ (((False ∧ p4) ∨ p5) ∧ True))) ∨ (p1 ∨ p4)) ∨ ((False ∧ False) → (((p3 ∧ p1) ∧ ((p3 ∨ True) ∧ p4)) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h7 := h4.left
  let h8 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654157216532285372591248724832 : (((((((p5 ∨ (((p2 → True) ∨ (((p1 ∨ p5) → False) → ((p2 ∧ p4) → (True ∨ True)))) → p2)) ∧ p3) ∨ p4) ∨ p1) ∨ (p2 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137676946411098988627856133676 : ((p1 ∨ ((((p5 ∨ (p5 ∨ (p4 ∨ p3))) ∨ (True ∨ ((((True ∨ (p3 ∧ p4)) ∨ False) ∨ True) ∨ False))) ∨ False) ∧ True)) ∨ (True ∧ (p2 ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602605735267500132415598651804 : ((((False ∨ ((True ∨ (((((True ∨ (p5 → (p3 ∧ (p5 ∨ p4)))) ∨ False) ∨ p1) → (p2 ∧ p2)) → ((p3 → p1) ∧ p1))) → False)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731250788851724724580491779033 : ((((p3 ∨ (False → p3)) → ((((p2 ∧ (True ∧ (p5 → ((p2 → p1) ∨ p4)))) → False) ∧ p5) ∨ ((p3 ∨ True) ∧ ((False ∧ p2) → True)))) ∨ p2) ∧ True) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219158023674782402090840523818 : ((False ∨ ((p4 ∨ p3) ∧ p1)) → ((p2 ∧ ((p1 ∨ p1) → ((p3 ∨ ((p1 ∨ p2) ∧ False)) → ((False ∧ p1) ∧ (p3 → (p3 → p4)))))) ∨ p1)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323922674191292729048945407686 : (p5 ∨ (((p3 → ((p3 ∧ True) → (True → ((True ∨ p1) ∧ ((False ∧ True) ∧ p1))))) ∨ p4) → ((p1 ∧ ((p2 ∧ p3) → (p2 → p5))) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141645619090071933569139250487 : (((p4 → (p5 ∨ p4)) → (p5 ∧ (p5 → (((p1 ∧ p3) ∨ (((p1 ∨ False) → False) ∧ p1)) → ((p5 ∧ p3) ∧ p2))))) → ((True → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68581129589496994580883362044 : ((p4 → ((((p3 ∨ p1) ∧ p2) ∨ (p2 → (p4 ∧ ((((False ∨ False) ∧ p2) → (False ∨ ((p2 ∧ (p5 ∨ p1)) ∨ False))) → p3)))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131277130683309043007100386256 : ((((p1 → p3) ∧ (p4 ∨ (p2 ∧ False))) ∨ (True ∧ (((p5 ∨ True) → (((p3 ∧ p1) ∨ (True ∨ p3)) ∨ True)) ∨ p2))) ∧ (False → (p1 → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54280693358578623695870569031 : ((((p3 → (p5 → p1)) ∨ ((p2 ∨ p2) ∨ True)) ∧ ((True ∧ ((p5 ∨ (True ∧ p3)) ∧ p2)) ∧ (False → (p4 ∧ ((p5 ∧ True) ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184547927548018025700147653549 : (((((p2 ∧ (False → (True ∨ p3))) ∨ True) → p2) → (False ∨ p4)) ∨ (((p5 ∧ False) ∧ (p3 → ((p5 ∧ p1) ∨ False))) ∨ (p5 → (p5 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66296546256749078575856675761 : ((p5 ∨ ((p1 ∨ p5) ∨ (((((p1 ∨ p1) ∧ p1) ∨ (p4 ∨ (p2 ∨ (True → True)))) ∧ (((p4 → p2) ∧ False) ∧ (p1 ∨ True))) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171402961861735498308747198906 : ((((p1 ∧ (p1 ∨ (p4 ∨ True))) ∨ (p3 → ((p4 → (p5 ∧ p1)) ∧ True))) ∧ p2) ∨ (p5 ∨ (((p1 ∧ p5) ∧ True) → (True → (False → p4))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357115963539099529633513173872 : (p5 → ((True → (p4 ∨ p3)) → (((False ∨ (((False ∨ p2) ∨ (True → ((p1 ∨ p5) ∧ p1))) ∨ p1)) → ((True → (p1 ∨ True)) → False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65653415810554805692855405843 : ((p4 ∨ ((False ∨ ((p4 ∨ (p1 → ((p2 ∧ (p2 ∨ (p5 → p2))) → ((p2 ∧ False) ∧ False)))) → (p1 → (False ∨ (False ∨ True))))) ∨ p5)) ∨ False) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228924933062914700388046374955 : ((p4 ∨ (p2 ∨ False)) ∨ (((True ∧ p5) ∧ ((p3 ∨ p2) ∧ (p5 → False))) ∨ ((True → (p3 ∨ (((False ∨ False) → p1) ∨ (p2 → True)))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187139136008620599112454487512 : (((p4 ∨ p1) ∨ (p4 ∨ ((p4 ∨ ((False ∧ p5) ∨ p1)) ∧ p3))) → ((False ∨ p3) ∨ (((True → (p4 ∧ p5)) → True) → (True ∨ (p4 ∧ p1))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- False on the left can always be used.
          apply False.elim h16
        case inr h18 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260779326698946697371786401373 : ((p3 → p5) → ((((((p5 ∧ (((p1 ∧ p5) → p4) → ((True ∧ p5) ∧ p4))) ∨ (p4 → p4)) ∨ p1) → (p2 ∧ p4)) ∨ False) ∨ (p2 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594165518381035416499271177562 : ((((((((p1 → p1) ∨ p1) ∧ p4) → (False ∨ (((p3 ∧ p4) ∧ p4) ∧ (p3 ∨ (p1 ∧ p4))))) → ((p2 ∧ True) → (p3 → False))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638198724012096992368315057527 : ((((((p4 → (p2 ∧ True)) → ((p3 ∧ p2) ∧ p5)) → (p3 ∨ (((True → p1) ∧ p3) → ((False ∨ (True ∨ (p4 → p1))) ∨ p3)))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40698370742217575590933655527 : (((((((((True ∨ ((p4 ∨ p2) → p3)) ∨ (p1 ∧ p2)) ∨ False) ∧ False) ∨ True) → ((p5 → p1) → ((p2 ∧ p5) ∨ p5))) → p1) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255102390329283934746832185012 : ((p4 ∧ p2) → (False ∨ ((((p4 ∨ ((p2 → p5) ∨ ((p1 → (p2 ∧ p5)) ∧ True))) → (p1 ∧ (((p5 ∨ p3) ∨ p4) ∨ p3))) ∨ p2) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134650183202487767485512974009 : ((((p2 → ((p2 ∨ (True → p4)) ∧ ((p5 ∨ (p5 → p4)) ∨ p4))) ∨ (((p5 ∨ (False ∨ False)) ∧ p2) ∧ p4)) → p2) ∨ (p1 → (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670318557030213802134663629789 : (((((p5 ∧ (True ∧ p5)) ∧ ((p4 ∨ p4) → ((p2 ∨ (True ∨ True)) ∧ ((False ∧ (p2 ∧ p1)) → (p5 ∨ p5))))) ∨ ((p3 → p2) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686561402763042377038399957221 : (((((p4 ∨ True) ∧ (True → (p5 ∧ (p4 ∨ (((True → p1) → (p5 → (True ∧ True))) ∧ p5))))) → ((p1 ∧ ((p2 ∧ p1) ∧ p4)) ∨ p5)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665115018469385250991465737496 : ((((p5 → (p1 ∧ ((True ∨ ((((p1 → (True ∨ p5)) ∧ (p2 → False)) ∧ p4) ∧ (p4 ∨ p1))) ∧ (True ∨ (p5 ∧ p3))))) → (p3 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705956216205501277979986775276 : (((((True ∧ (p2 ∧ p1)) → ((p4 → p4) ∨ p3)) ∧ (((False ∨ (p3 ∨ False)) ∧ p2) ∨ (p4 ∧ ((p5 ∧ p5) ∧ ((p3 ∨ p3) ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197573286177991433952608277513 : ((((True ∧ p3) → (p2 ∧ p4)) ∨ (p1 ∧ p1)) ∨ ((p2 ∧ ((False ∨ ((True → True) ∧ (p2 ∧ (p5 ∧ (False ∧ p5))))) ∨ (p1 ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300157639905375855818522494226 : (False ∨ ((True → (False ∧ (((p5 → p4) ∨ (((p3 → p1) ∨ (p3 ∧ (p2 ∨ p5))) ∨ p1)) → (((p3 ∧ True) ∧ p2) ∨ False)))) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749324573149649892051757471371 : (((True ∧ (((((p3 ∧ (((p3 → (False ∨ True)) ∨ p3) ∨ (p5 ∧ True))) → (p1 → ((p2 ∧ p5) ∨ (p5 ∨ p3)))) ∧ p5) ∧ p5) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342871581505057373895372234103 : (p2 → ((p5 ∧ ((p5 ∧ (p5 ∧ False)) ∨ p5)) ∨ ((((p1 ∧ p1) ∨ p4) ∨ ((((False → (p1 ∨ p5)) → p1) → p4) ∨ (True ∨ p1))) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714667331683485244704668055916 : (((((True ∨ p4) → (False → (p1 ∨ True))) → (p4 ∧ ((((False → (p3 → (True → p5))) → p4) → (True → (p4 → (p5 ∨ False)))) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158076175152195292739854158053 : (((((p4 → p3) → p5) ∨ (p5 ∨ p1)) → ((((False → p3) ∧ p3) → True) → (p1 ∨ (True ∧ p3)))) ∨ (p1 → ((True ∧ p1) → (True → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112794407323127315103328363372 : (((((False ∧ ((p1 → False) → True)) → p3) ∧ ((p1 → (p2 → p2)) → ((False → (((p1 ∨ p2) ∧ p4) → True)) ∨ p3))) → p5) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303186228552842930811874738302 : (False ∨ (p4 → (((((p4 ∧ ((p4 → p3) → (p4 → (p5 ∨ p4)))) ∧ p2) → True) ∧ p5) → (((p1 → (p1 ∨ p4)) ∧ p4) → (p3 ∨ p5))))) := by
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
  let h6 := h2.left
  let h7 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50364669322964200848922459489 : (((((True ∧ False) ∧ p3) ∨ ((p4 → ((p3 ∧ p2) → False)) ∨ ((p5 ∨ (p5 ∧ p2)) ∨ (p1 → p1)))) ∨ (((p5 ∨ False) ∨ True) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630727231829357938143934412235 : (((((p3 → ((((p3 ∨ p5) ∨ p1) ∧ ((True ∧ (p2 → p3)) → ((p3 → p1) ∧ (False ∧ (p1 ∨ (p3 ∨ True)))))) ∧ p4)) ∨ True) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305488430810755662915661188662 : (p1 ∨ (((((p1 ∧ p5) → p4) → (p4 → ((p1 → p1) → (p3 ∧ p1)))) ∧ p5) ∨ (True → (p2 ∨ ((True ∨ ((p1 ∨ False) ∧ p4)) ∨ p3))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66458984282549553088603619165 : ((True → (((p2 ∧ p4) → ((p1 ∧ (((p4 ∧ (p3 ∧ ((p5 ∨ False) ∨ p5))) ∧ (p2 → (p3 ∨ p2))) ∨ (p4 ∨ p5))) ∧ False)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191897693874387760571718320027 : ((p5 ∨ (((p1 ∨ p3) → ((True → p4) → False)) → p2)) ∨ ((p2 ∨ ((p2 → ((False ∧ p3) ∧ (p2 ∧ (p3 → p1)))) → (p4 → p4))) ∨ False)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313977487220876365136667078986 : (p3 ∨ ((((p1 ∧ (p3 ∧ (p4 → (p1 ∧ p3)))) ∨ (p1 → True)) ∨ ((p3 ∨ p1) → ((p4 ∧ False) → ((p4 ∧ False) ∨ True)))) ∨ (p4 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303912168149777867292266373899 : (p1 ∨ ((((p4 ∧ ((False ∨ p1) ∧ p4)) ∧ ((p4 ∨ p5) ∧ (p1 → True))) ∨ (False → (p2 → (p2 → ((p5 → p2) ∨ (p1 ∧ p3)))))) ∨ p3)) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315426657105455738914695160838 : (p3 ∨ ((p3 ∧ (p4 ∨ p2)) ∨ (((p3 ∨ (p4 ∨ True)) → (p1 ∧ ((p3 ∧ p2) ∨ (p2 ∨ (((p2 → p4) ∨ False) ∨ True))))) ∨ (p1 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150487544279718262119825777084 : ((((((p1 ∨ ((p5 ∧ (p2 ∧ p3)) → (False ∧ p4))) → p5) ∧ ((False → False) → p2)) → (True → True)) ∧ p5) → ((p4 → p3) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315903138053627534483805507048 : (p3 ∨ (True ∧ ((p4 ∧ ((((False → ((p4 ∨ p5) ∨ False)) ∨ p5) → p5) → True)) → (((p1 → (True → ((p4 → p2) ∧ True))) ∧ p3) ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_546754041767280922201868593975 : (((False ∨ ((((False ∨ p2) ∧ ((p4 → True) ∨ False)) → (((p2 ∧ p2) ∧ ((p5 → p3) ∨ p3)) ∨ (True ∨ (True → (p1 ∧ p3))))) ∧ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187655055836737135764045802507 : ((True → (((p2 ∧ (p1 ∧ p4)) → (p3 → (False ∧ p1))) ∧ p2)) → (((((False ∨ (p1 ∧ False)) ∧ ((True → p2) ∨ True)) → True) ∧ p2) ∨ p3)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737128930803489929771005940875 : ((((p3 → p4) ∧ (((((((True ∧ (p1 ∧ ((p2 ∨ (p4 ∨ p3)) ∨ ((True ∨ False) → p2)))) ∨ p1) → p3) ∧ p3) ∧ p5) ∨ p4) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160364317650004876509407518938 : (((((((False ∧ ((True → p4) ∨ p2)) ∨ False) → False) ∨ p1) ∧ (p1 → p3)) ∧ ((p1 ∧ p4) → p1)) → ((p4 ∨ (True ∧ (False ∨ False))) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693662706929539663430450015239 : (((((((p3 → (p3 → (p4 → p2))) ∧ (p2 ∨ p1)) → (False ∧ True)) ∨ p5) ∨ (((p2 ∧ True) → p4) → ((p1 ∧ (p3 ∨ p5)) → p1))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303186122652781367431419868174 : (False ∨ (p4 → ((p5 ∧ ((p1 ∨ (((True ∨ True) → ((False ∨ p2) ∧ p5)) → p1)) ∨ True)) ∨ ((p2 → (p4 → ((p3 ∨ p4) ∧ p1))) → True)))) := by
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
theorem thm_5_vars_40529352881966459621846280113 : ((((p1 ∨ (((((False ∧ ((p1 ∨ (((False ∨ p1) ∨ (p2 ∧ (p2 ∨ p3))) → p2)) ∧ False)) → p5) ∨ p5) ∧ p4) → p2)) ∨ True) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149091349551530306823136010164 : (((p4 ∧ (p5 ∨ p4)) → (((p2 ∨ (p3 ∧ False)) ∧ (p2 ∨ p1)) ∧ ((True ∨ p5) → ((False ∨ False) ∧ p5)))) ∨ (p1 → ((False ∨ False) → p2))) := by
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110998716206053697379288532658 : ((((((p5 ∨ (True ∨ p1)) ∨ (True ∨ (p2 ∨ p3))) ∨ (((p1 → (True ∧ p1)) ∨ p3) → p3)) ∧ (True ∧ (p3 ∧ p3))) ∧ p4) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337542235639030896178910823638 : (p1 → (((True → (p1 ∨ (True ∧ p5))) → (((p1 → ((False ∧ ((p3 ∨ p2) → p3)) → False)) → p5) ∨ True)) ∨ ((False ∨ (p3 ∨ p1)) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324092781377110575610946292379 : (p5 ∨ ((p2 ∨ ((((p4 ∧ (p1 ∨ p4)) ∧ (p4 → p5)) → p3) → p4)) ∨ (False → ((((((p4 → p5) → True) → p2) → p4) → p2) → True)))) := by
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
theorem thm_5_vars_47541359794967785079835350527 : (((p5 ∨ (((((p1 ∧ p5) ∨ ((p5 ∨ ((False ∨ p3) ∧ ((p1 ∨ p1) ∨ p3))) → p2)) ∨ p3) ∨ True) ∧ (p4 → p3))) ∨ (False ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178863898243600017107028192367 : (((False → (p5 ∨ p5)) → (((((p3 ∧ True) ∧ p3) → p3) → p2) ∨ True)) ∨ ((p3 → p1) → ((((p5 → (False → p4)) ∧ p5) ∨ p4) ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232183043992801759967665859100 : (((False → False) → p3) → ((((p1 ∨ ((True → p3) ∨ p1)) → (p3 ∧ (p2 ∧ (p5 → False)))) ∧ (False → p3)) ∨ (True ∨ (False ∧ (True → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112059358952970044763306330129 : ((((p5 ∧ p5) ∧ ((((p1 ∧ (p3 ∨ (p5 → p1))) → p3) ∨ ((p5 → p1) → (True ∧ (True ∧ True)))) → (p2 ∨ p5))) ∨ p2) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784732554417926858374177634689 : (((p3 ∨ (p5 ∨ (((((p5 ∨ (p5 ∨ (p1 ∨ p3))) ∧ (p1 ∧ p4)) ∧ p1) ∨ (False ∧ (True ∨ (p4 ∨ p1)))) ∨ ((True → p2) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52679830195765754098656660120 : (((p3 ∨ (((False → (p5 ∧ (p3 ∨ (p2 → p5)))) → (p1 → False)) ∨ p3)) ∨ ((True ∧ (p4 → True)) → ((True → True) ∨ (p1 → False)))) ∨ p5) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_99183264855424993655663943673 : ((True → (True → (False ∨ ((((p4 → p5) ∨ True) → False) ∧ ((p5 ∧ (False → p5)) ∧ ((p2 → ((p2 ∨ False) ∧ (p4 → True))) → True)))))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h14 : ((p4 → p5) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h15 := h8 h14
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158744627055817963870723561380 : ((p4 ∧ ((((((False ∧ p1) ∨ ((p1 → ((p5 ∧ p5) ∧ p4)) → False)) ∨ p4) ∨ p2) ∨ p5) ∨ True)) ∨ ((p2 ∨ ((p5 → p3) ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66816544476088369126651321625 : ((True → (p5 ∨ (p3 ∨ ((p5 ∧ p4) ∨ ((((((((((p5 ∨ p1) ∨ p5) → p3) → p2) ∧ p5) → p4) ∧ False) ∨ p2) ∧ p2) ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94186246538363294016723508814 : ((p2 ∧ ((p2 ∧ (((True → p2) ∧ p2) → ((True ∧ p3) ∧ ((((False ∧ p3) → (p1 ∧ p3)) ∧ ((False ∨ p1) → p5)) ∧ p4)))) ∨ p4)) → p4) := by
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
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : ((True → p2) ∧ p2) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h5
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h7
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230479154214575274342206508992 : (((p5 ∨ p5) ∧ p3) → ((((False ∨ p3) → ((((False → p2) ∨ False) → True) ∨ (p2 ∨ (p3 → ((p5 ∨ p4) ∧ p2))))) → p4) ∨ (p5 ∨ p5))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150259056877376368757853233846 : ((p3 → ((p4 → ((p2 ∧ p3) ∧ p5)) ∨ (p2 → (((p1 → (p1 ∧ False)) ∨ ((p5 ∧ True) ∧ p3)) → p5)))) ∨ (False ∨ ((p2 ∨ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190683578275068714358065764278 : (((p4 → (p4 → ((p1 ∨ (True ∧ p4)) → True))) → False) ∨ (p1 → ((p1 → (((p1 ∧ True) ∨ p5) ∧ p2)) ∨ (False → ((False → p4) → False))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221625844609295525608527223199 : (((p5 → True) ∨ False) ∧ ((p4 ∨ ((((p3 → (p3 → (p3 ∧ False))) → ((True → (p4 ∧ True)) ∧ (p1 ∨ (p1 → p3)))) ∧ p3) → False)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47443240281275892288125641481 : (((p3 ∧ ((((p2 → (p2 ∨ p5)) → ((((p2 ∨ p5) → (p4 ∨ False)) ∨ p2) → p4)) → False) ∨ (p5 → (True ∨ p1)))) ∨ (p3 → p3)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225338271164067356561672573547 : (((p1 ∨ p1) ∧ p1) ∨ (((p3 ∨ p1) ∨ p4) → (((p3 → ((p5 → p4) ∧ ((False → p4) → (True ∨ ((p5 ∧ p1) ∨ p3))))) ∨ True) ∨ p1))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150602563482927400627639713766 : ((((p4 ∨ p3) → ((p1 ∧ ((((p5 → p5) → (p2 ∧ (False ∨ False))) ∨ (p2 ∨ True)) ∧ p5)) ∧ p2)) ∧ p3) → ((p5 ∧ (p2 ∧ p5)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p4 ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h11 : (p4 ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h12 := h9 h11
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- One of the premise coincides with the conclusion.
  exact h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
  have h16 : (p4 ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15
  -- We have shown the premise of h14, we can now drive its conclusion.
  let h17 := h14 h16
  -- We need to get the left conjuct of h17 based on <expert-advice>.
  let h18 := h17.left
  -- We need to get the right conjuct of h18 based on <expert-advice>.
  let h19 := h18.right
  -- We need to get the right conjuct of h19 based on <expert-advice>.
  let h20 := h19.right
  -- One of the premise coincides with the conclusion.
  exact h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83365389408620262098827660124 : ((((True ∨ p5) → ((True ∧ ((((True ∧ (p4 ∧ p1)) → (True ∧ p4)) → True) ∨ p1)) ∧ p2)) ∧ (p5 ∧ (True ∨ (p5 → (p1 ∨ p3))))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (True ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : (True ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137079671163750077452793642652 : (((p5 → p4) → ((False → p5) ∧ (((p3 ∧ (p4 ∧ p1)) ∨ p2) ∨ ((p1 ∨ True) ∨ (p3 ∧ (p4 ∧ (p1 → p1))))))) ∨ (p4 → (p5 ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118381306821834201182243841006 : ((p2 ∨ ((((p5 → ((True ∨ False) → p1)) ∨ False) → ((p4 → p3) ∧ False)) → (((False ∨ p1) ∨ (p1 ∧ p3)) → (True ∧ p5)))) ∨ (p2 ∨ False)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h6 : ((p5 → ((True ∨ False) → p1)) ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- Implications on the right can always be decomposed.
        intro h8
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h10 =>
          -- False on the left can always be used.
          apply False.elim h10
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h11 := h1 h6
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h16 : ((p5 → ((True ∨ False) → p1)) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h20 =>
        -- False on the left can always be used.
        apply False.elim h20
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h21 := h1 h16
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354561488617414601299176033535 : (p5 → (((((((False ∨ (p3 ∨ (p3 ∨ (((p5 ∨ True) → p1) ∨ (p5 ∧ p2))))) ∧ p3) ∨ ((False → False) ∨ p1)) ∧ p1) ∨ p2) ∧ False) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148255819229580756437354804058 : (((False ∧ ((True ∨ (p2 ∨ p4)) → (True ∧ ((p3 ∧ (p1 ∨ p5)) ∨ (p5 ∧ p5))))) ∨ (True → (p5 → p5))) ∨ ((True → (True → False)) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157123799490778092509923284082 : ((((((p1 → (((((False ∨ p2) ∧ p2) → p3) ∧ p2) → p4)) ∨ False) → (p1 ∨ p5)) ∧ p4) → p5) ∨ (((False → p5) ∨ p4) ∨ (p2 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136440298907530055506859032928 : ((((False ∨ True) → (p4 ∨ p2)) → ((p2 → p3) ∧ (((p4 ∧ False) ∧ p2) ∨ (p5 ∧ ((False → p1) ∧ (p2 ∨ False)))))) ∨ (True ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112650629933668438976932959290 : ((((((p4 ∨ ((((p1 ∨ p3) → p3) ∨ (True ∨ p1)) ∧ p4)) → p3) ∧ ((False ∨ p3) → p4)) ∧ (p5 ∧ (p4 → p4))) → False) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356027270407392097409008783893 : (p5 → (((p1 → (((p3 ∨ ((p2 ∧ (p2 ∨ p5)) → False)) ∧ p5) ∧ p3)) ∧ (p5 ∨ ((p4 ∧ p3) → p3))) ∨ (((False ∧ p5) ∨ False) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148527798434505490688136324273 : ((((p5 → ((False ∨ p3) → False)) ∨ (False → ((False ∨ p5) ∧ p1))) → (True ∧ ((p5 → p1) ∨ (p2 → p3)))) ∨ (False → (p5 ∨ (p2 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609496186963112751094200613702 : (((((p1 ∧ ((p5 ∧ (False → (p2 ∧ ((p3 ∨ (p2 → False)) ∨ (True ∨ False))))) → (((p2 → p2) ∧ p3) ∧ (False ∨ p1)))) ∨ p2) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_110995438909124910616888899312 : ((((((True ∨ (True ∧ ((p4 → (((p4 ∧ (False ∨ False)) ∨ False) ∨ p2)) → False))) → p3) → p2) ∧ ((p5 → False) ∨ p3)) ∧ False) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



