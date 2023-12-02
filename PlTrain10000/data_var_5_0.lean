variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311827945154653248203199070505 : (p2 ∨ (p1 ∨ ((p4 ∧ (p3 → (((p1 → p2) ∨ p2) ∧ (p2 → p2)))) → (p4 → (p4 → ((((True ∨ p5) ∨ p4) ∧ (p4 → p2)) → p2)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h1.left
      let h10 := h1.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h11 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h12 := h6 h11
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h1.left
      let h15 := h1.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h16 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h17 := h6 h16
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h1.left
    let h20 := h1.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h21 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h22 := h6 h21
    -- One of the premise coincides with the conclusion.
    exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51448996630014483097891051906 : (((((p5 → (((p1 ∨ p3) ∧ p5) → ((False ∨ p3) ∧ p5))) ∧ True) ∨ (p1 ∨ (p5 → False))) → ((p4 ∨ p3) ∧ ((p3 ∨ p4) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233435474824186039596483976075 : ((False ∨ (True → p1)) → (((p5 ∨ (p3 → ((True ∧ False) ∨ p1))) ∧ p5) ∨ ((p4 ∧ ((((p4 ∧ p5) ∧ (False → p1)) ∨ p5) ∧ False)) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751879108622766682466530979154 : (((True ∧ (p2 ∨ ((p1 ∨ ((p5 → (((False ∧ p1) ∨ (p4 ∨ (p4 → (p3 ∧ ((True → p1) ∧ p1))))) ∧ p1)) ∧ p1)) ∨ (False ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612480962399722631396021041824 : ((((((p3 ∧ ((p2 ∧ (False → p5)) ∧ (p4 ∨ ((((True ∧ ((p2 → p3) ∧ False)) ∧ True) ∨ p4) ∨ p3)))) ∧ p3) ∨ (False ∧ True)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_134028666370448187956889956221 : (((((p1 → (((True ∨ (p2 → (p1 ∨ p4))) ∨ p5) ∧ ((((p3 → p5) ∧ p2) → True) ∨ p3))) → p2) ∨ True) ∨ p2) ∨ ((p2 ∧ p3) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225660039522838941953717116766 : (((p2 → p2) ∧ p3) ∨ ((p5 → (p1 ∨ ((p2 ∧ (True → ((False ∧ (False ∨ p3)) ∨ ((p5 → p5) ∧ True)))) ∨ ((p1 → p5) → p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118349705410814067521196087432 : ((p2 ∨ ((((p2 ∨ (((p5 ∧ ((p2 ∨ p1) ∧ p1)) ∧ (p2 → ((p4 ∧ p3) ∨ p4))) → True)) → p1) ∨ (p1 ∨ p1)) → p4)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315036993701166931708221328783 : (p3 ∨ (((((p2 → p3) ∨ p4) ∨ (p2 → False)) ∧ p1) → (True ∧ ((((p4 ∧ p4) → True) ∨ False) ∧ ((p3 → p2) ∨ (False → (p1 ∧ False))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h15
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h17
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h19
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h19
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64912429650953323388782613221 : ((p2 ∨ (((p3 → (p1 ∧ p3)) ∧ ((p3 ∨ (p5 → True)) ∧ (((p2 → p1) → p1) ∨ (p1 ∨ p3)))) → (p4 ∧ ((p3 ∨ p5) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265696740282909772874246419994 : (True ∧ (p3 ∨ (((p4 → True) ∧ ((p5 ∧ ((((True ∧ p1) ∨ (((p2 ∧ p1) ∧ ((p3 → p4) ∨ True)) → p3)) ∧ p4) → p1)) ∨ True)) ∨ True))) := by
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
theorem thm_5_vars_251306239885088562223422557703 : ((p2 → p3) ∨ (((p3 ∧ (True ∧ p2)) ∧ (((False ∨ (p2 ∨ p4)) → True) ∧ (((((p2 → p4) ∧ p5) ∧ p5) ∧ p2) ∨ p4))) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307204186735330118155030050999 : (p1 ∨ (p1 ∨ (((((p5 ∨ p4) ∨ ((False → p5) ∨ p5)) ∧ p3) ∨ p5) ∨ ((((p2 ∧ p4) ∧ True) → (p5 → (p3 ∧ True))) → (True ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190358436170554205524338510254 : ((((p1 ∧ p3) ∧ (p4 ∧ ((p4 ∨ p4) → p1))) ∨ False) ∨ ((((p2 → ((True ∧ (p2 → p3)) → ((p2 → p4) ∨ True))) → p3) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136671785968624177156124966090 : (((p3 ∨ (p5 ∨ p4)) → (((p5 ∨ p1) ∧ ((False → True) → True)) ∨ ((p2 ∧ p3) ∧ ((False → p3) ∨ (p1 ∧ False))))) ∨ ((p4 ∧ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353351499150644793541958823081 : (p4 → (False ∨ (((p4 → ((p1 ∨ (((p1 ∧ p5) → p2) ∨ p2)) → True)) ∧ ((((p1 → False) ∨ p2) ∨ False) → (p2 ∧ (p2 → False)))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338398194529565665286488365067 : (p1 → (((True ∧ (True → p2)) ∨ p5) → (p4 ∨ (((p3 ∧ (p4 ∨ p1)) → (((p5 ∨ (p2 → p4)) ∨ (p3 ∧ p1)) ∨ (p2 ∧ p2))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
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
theorem thm_5_vars_338972651353994757943598458967 : (p1 → ((p3 → False) → (p1 ∧ (p2 ∨ ((p3 ∧ p2) ∨ ((((((True → p1) ∨ p5) ∨ p1) ∧ (p5 ∨ (p3 ∨ True))) ∨ True) ∨ (True ∧ p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
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
theorem thm_5_vars_134356412116219062282786166963 : (((False ∨ ((p2 ∧ (p2 ∨ ((p3 → False) ∧ ((p1 ∨ ((p2 ∨ (True ∨ (False → p4))) ∧ p5)) ∧ True)))) → p3)) ∨ p2) ∨ (p5 → (p3 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317621594136444136025030957616 : (p4 ∨ (((((p4 ∧ (((p3 → (p1 ∧ (False ∧ p2))) ∨ (p2 ∨ p4)) ∨ (p5 ∨ p3))) ∨ (p2 → (True ∧ (False ∨ False)))) → p5) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164955428910147985256701004276 : ((((True ∧ (p2 → ((p3 ∧ p2) ∨ (False ∨ (((True ∨ p1) ∨ True) → False))))) → False) → False) ∨ ((((False ∧ True) → (p3 → p4)) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244657637752064904533837320254 : ((False ∧ p5) ∨ (False ∨ (p2 → (((p1 ∨ (p2 ∧ (True → False))) ∨ (p2 → (((False → True) → (p4 ∧ p2)) ∨ (p3 → p2)))) ∧ (p5 → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_34427154885001686767999660866 : ((True → (False ∨ (p4 ∨ (((p3 ∨ (p3 → p2)) ∧ (((p1 ∧ False) ∨ (p3 ∧ p5)) ∧ (p3 ∨ False))) ∨ (p4 ∨ ((True ∨ p4) → True)))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50219052794348771561006051238 : ((((((p1 → False) → p3) → (False ∨ (p2 → ((p1 ∨ p1) → (((p3 ∧ p3) ∨ True) ∧ True))))) ∨ p2) ∨ ((p5 ∧ False) → (p4 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59563429669094906333370665339 : (((p3 → p4) ∨ ((((p3 → (False ∨ ((False ∧ (True ∨ (p2 → ((p2 → (False ∨ (p1 → p4))) → p3)))) ∧ p2))) ∨ False) ∧ p1) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619187486678634999411641478340 : (((((True → (p4 ∨ p4)) ∨ (((True ∨ (True → (False → p5))) → p4) ∨ (True ∨ (p5 ∧ (False ∨ (False ∧ (False → (p4 → True)))))))) ∨ False) ∨ False) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258884831617688654908005016681 : ((True → p2) → ((((p1 → ((((p5 ∧ p3) → p3) → ((p2 ∨ (p3 → p4)) ∨ (p2 ∧ ((False ∧ p4) ∧ p5)))) ∨ p4)) ∨ True) → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65161450635224448333758968092 : ((p3 ∨ (((((p2 ∧ (True ∨ (p2 ∨ (p2 → (((p1 ∧ p2) ∧ p2) ∧ p2))))) → True) → (p5 ∨ ((p2 ∨ p5) ∧ p4))) ∨ True) ∧ True)) ∨ p4) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166384548016091668598138825756 : ((False ∨ ((p3 ∧ ((((True ∧ (p1 ∨ p5)) ∨ (p3 ∨ p2)) → False) → p3)) ∨ (p3 ∨ p2))) ∨ (True ∧ (((True ∨ p4) ∧ (False ∧ True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157956838452879717149463630708 : ((((p1 ∨ (p1 ∧ (p1 ∧ (p2 ∨ p3)))) ∨ p1) ∨ (p5 → ((False → ((p1 → True) ∧ False)) ∨ p2))) ∨ ((p3 → (True → p2)) → (p3 ∨ p5))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337378969760655461063417217558 : (p1 → (((p1 ∨ False) ∧ (((True ∨ (((p1 ∨ p4) → p1) → (False → (((p2 ∨ p3) ∨ p2) → True)))) ∨ p1) → False)) ∨ (p4 ∨ (True ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_477404064484984095300522404031 : (((((p5 ∨ ((p3 ∨ (False ∨ p2)) → (False → p3))) ∨ p5) → ((((False ∧ p3) ∧ False) ∨ (p2 → ((p4 → p5) ∧ p5))) ∨ (False ∨ True))) ∧ True) ∧ True) := by
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
  case inr h5 =>
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
theorem thm_5_vars_136575540555624997153713873668 : ((((p4 → p4) → False) ∨ (((((p1 → p5) ∨ (p4 ∨ p3)) ∧ p5) ∨ (False ∨ p1)) ∨ ((False → (p5 ∨ False)) ∨ p2))) ∨ ((p5 ∧ p3) → p5)) := by
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
theorem thm_5_vars_56191385242136060114767747839 : (((p5 ∧ ((True ∨ p1) ∧ p3)) ∨ ((p5 ∨ (((((p5 → (p1 → (p3 ∨ p1))) ∧ (p5 ∧ p3)) → (p2 ∧ p4)) ∨ p2) → p5)) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142608131782331838566194908156 : ((False ∨ (((p2 → p4) ∨ (False → False)) → ((((p3 → p4) ∨ (p5 ∨ (p1 ∧ p2))) ∨ p1) → (p2 ∨ (p4 → p3))))) → (p4 → (p3 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : ((p2 → p4) ∨ (False → False)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (((p3 → p4) ∨ (p5 ∨ (p1 ∧ p2))) ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h8
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h13 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h14 := h12 h13
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49748101067616224219338813184 : (((p4 ∧ (p4 → (((p4 → p3) ∧ (p2 ∨ p5)) ∧ ((p1 ∧ p3) → (((p5 ∧ p2) ∧ False) ∨ (p3 ∨ p4)))))) → ((p5 ∨ p1) ∨ p2)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184062352822568743893557937654 : ((((((p4 ∧ False) → p4) ∧ (True ∧ p4)) → (p3 ∨ p2)) ∨ p1) ∨ (p1 → ((p4 → p2) ∨ ((p2 → p1) ∨ (((p3 → p2) → True) ∨ p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51252592610615866478130809651 : ((((p4 ∨ p4) ∧ ((p1 ∧ True) → ((False ∧ p2) ∨ (((True → p4) ∨ (p2 ∨ p3)) ∨ p4)))) ∨ (((False ∨ p2) → (p5 → p2)) ∨ p1)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808670877613065559971063203508 : (((p4 → (p1 → (False ∧ ((p5 → (p5 → p2)) ∨ ((p5 ∧ p1) ∨ ((p5 ∧ (p4 ∨ p3)) ∧ (((p5 ∧ p5) → p3) ∧ (True ∨ p3)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309821662412318010512714250413 : (p2 ∨ ((p3 → (((((((p2 ∧ (p3 ∨ p4)) ∨ False) ∧ p1) → (p3 ∧ p4)) ∧ (p2 ∨ p2)) ∧ p4) ∨ p3)) ∨ (p4 ∧ ((p2 → p3) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180698319083507407646242034892 : (((((p2 → False) → p1) ∧ True) ∧ (((False → p2) ∨ False) ∧ (p3 ∧ True))) → ((p5 ∨ ((True ∨ (p5 → p1)) ∧ (p3 → p2))) ∨ (p5 → p5))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157610192687084073931954404426 : ((((((False → p2) → (p1 → p5)) ∧ ((p2 ∨ (p1 ∧ True)) → p5)) ∨ p3) ∧ ((p1 ∧ p4) ∧ p4)) ∨ ((p4 ∧ (p5 ∧ False)) → (p4 ∨ p1))) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740990491653353390285041188942 : ((((p3 ∨ p4) ∨ ((p1 ∧ ((p2 ∧ ((True ∧ False) ∧ (True → (False ∨ ((p3 ∧ True) → (p3 ∨ False)))))) ∧ (p1 ∧ p2))) ∧ (p1 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641608054274420198986721922557 : (((((p5 ∧ False) → (((p3 → (p3 ∨ (p2 → (p2 → p5)))) → (((p1 → (False → (True ∧ p3))) ∧ (p1 ∧ True)) → True)) ∨ True)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169033777367353046522471402270 : ((p2 → (((((p3 ∧ (p4 → p2)) ∨ (p2 ∨ p3)) ∨ p5) ∧ p1) → (False ∧ (False ∨ True)))) → (((True → p5) ∨ ((p5 ∨ p5) → True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157355256292980427390669177700 : (((False → ((((p1 ∧ p4) → ((p3 → p1) → p5)) ∧ ((False → True) → (False → p3))) ∨ p1)) → p4) ∨ (p1 ∨ ((p4 → (p1 ∨ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342147395685560452859744646776 : (p2 → ((((p4 ∨ (p3 ∨ ((p2 → p2) ∧ (((p2 ∨ (p3 → p4)) ∧ (p3 → p3)) ∧ p2)))) ∧ p3) → False) ∨ (False → ((p3 → p1) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65135048707271733326435346394 : ((p2 ∨ (p2 → (((p2 → (p4 ∧ False)) ∧ (p3 ∨ ((p4 → ((p4 ∧ (p2 ∨ (False ∨ (False ∨ (p4 ∧ p3))))) ∨ p4)) ∨ p5))) → p5))) ∨ p3) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h11
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323271791080840052070597704827 : (p5 ∨ ((True → ((((p5 ∨ ((False ∨ p2) ∨ (False → True))) ∨ False) → (((p4 → ((True ∧ True) ∧ p5)) ∧ p5) ∧ True)) ∧ p3)) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4166935195846333632928647581 : (p4 ∨ (((False → p5) ∧ (p3 → (((p3 ∧ False) ∨ p2) → (p5 → (p3 ∧ p4))))) → (p5 ∨ ((False ∧ (False ∨ (p4 ∨ p3))) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_303795652114082148305009181506 : (p1 ∨ (((((p1 → p4) ∨ ((True ∧ (p5 ∨ (False ∧ p1))) → (((p4 → p4) ∧ ((p4 ∧ True) ∨ p4)) ∧ False))) ∨ (True → p5)) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345547581269211698155210271760 : (p3 → ((((p5 → (p3 ∨ (p3 → False))) → False) ∨ (((p4 ∧ (False ∨ (True ∨ p3))) → p5) ∧ ((p3 ∧ p3) ∨ ((p1 ∨ p5) → False)))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352120600131461350851819689213 : (p4 → ((p2 ∨ (p3 ∨ (p1 ∧ (p3 ∨ False)))) ∨ (p4 ∨ (False ∨ ((p5 ∨ (p2 ∨ (p5 ∨ ((p1 ∧ False) → (False ∧ p4))))) → (p3 ∧ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207496793431872474731136771956 : (((p5 → ((p2 ∧ p4) ∧ p5)) ∨ True) → ((True ∨ p1) → ((p3 → True) → (True → (p4 ∨ ((False ∧ ((False ∨ p3) ∨ True)) → (False → False))))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657985309307891790774394321112 : ((((p2 ∧ ((p1 → (p4 ∧ ((((p3 → (p2 ∧ p2)) ∨ p5) ∧ (((p3 ∨ p1) ∧ p3) → False)) → p4))) ∨ (p1 → False))) ∨ (p3 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344755625412402582011172529525 : (p2 → (p3 → (p1 ∨ ((p3 → (((False ∨ p2) → (p1 ∧ p4)) → (((True → p5) ∨ False) ∨ ((p4 ∨ (False ∨ p1)) ∨ p2)))) ∧ (p4 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225301151259714208671417895956 : (((False ∨ p1) ∧ p4) ∨ ((((p3 ∧ (p4 → p1)) → (p4 ∨ p2)) ∧ (p2 ∧ ((True → (True → True)) → p3))) ∨ ((p5 ∨ True) ∨ (p2 → p2)))) := by
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
theorem thm_5_vars_111080432472196382428395428929 : ((((((p5 → (p5 ∨ (p1 ∨ p5))) → ((p3 → True) → p3)) ∨ p2) ∧ ((p3 ∧ (p2 ∧ ((False → True) ∧ p5))) ∨ p1)) ∧ p5) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148038397985202551942164516699 : ((((True → p4) ∨ ((p2 → p2) → (True ∧ ((((p1 ∨ p2) → True) → p2) ∨ (p4 → p3))))) ∨ (p2 → p2)) ∨ (((True ∨ p1) ∨ p1) ∨ False)) := by
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
theorem thm_5_vars_315026965869496794339817187775 : (p3 ∨ ((p3 ∧ (((p2 ∨ p5) → True) → (p3 ∧ p3))) ∨ ((False → (p1 → ((((((p5 → p3) ∧ p3) ∧ False) ∨ p1) → False) ∧ p2))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337867015775377603018055197746 : (p1 → (((p2 → p1) ∧ ((False ∨ ((p4 ∧ p5) → p5)) ∧ (p1 ∧ (p4 ∧ False)))) ∨ ((p3 ∧ ((True ∧ p2) ∧ p4)) ∨ ((p4 → p4) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2465461591328069838100034074 : (((p2 ∧ p2) ∨ (((p4 ∨ (p4 → p3)) ∧ p3) ∨ p4)) ∨ (((False ∨ True) → (((True ∧ (p1 ∧ (p5 ∧ p2))) ∨ p2) ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64443657774339247913300633023 : ((p1 ∨ ((p3 ∧ (((p4 ∧ p3) → p3) → (p1 → ((p2 → ((True ∧ (False ∧ False)) ∨ ((False → p1) ∨ p4))) → False)))) ∨ (p5 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262163530408352939749094934748 : (True ∧ ((((p1 ∧ p3) → (((p3 ∨ (((p1 ∨ True) ∨ (p5 ∨ p2)) → p1)) → ((p5 ∧ p2) ∧ True)) ∧ (p2 ∨ (p3 → p1)))) ∨ True) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178787793807429868240346652856 : (((p4 → (p4 → p4)) ∧ ((p2 ∨ (p4 → True)) → (p4 ∧ (False ∨ False)))) ∨ ((False ∨ ((p1 → (p1 → (p1 → p5))) ∨ (p4 → p4))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54149981010256749796406688908 : (((p1 → ((p3 ∨ True) → (((p4 → p1) → p1) ∨ p3))) → ((p5 ∨ (((True ∧ (False ∧ p1)) ∧ (p4 ∧ False)) ∧ (False → p5))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64602216949058706659901334560 : ((p1 ∨ ((True ∧ p2) → (((p3 ∧ p3) ∧ (False ∧ (p5 ∧ (p4 → (True → ((False → p4) → False)))))) ∨ ((True ∧ (p5 ∨ p1)) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314436782558903813778161265472 : (p3 ∨ ((p4 ∧ ((p1 ∧ p2) ∧ (((p3 → (p1 ∧ (p3 ∨ p3))) ∧ (p3 ∨ (p2 ∧ p1))) ∨ (p3 ∧ p3)))) ∨ (p4 ∨ ((p5 → False) ∨ True)))) := by
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
theorem thm_5_vars_55143461992727659528957668944 : ((((((p3 ∨ False) ∨ p4) ∨ p3) ∨ p1) ∨ ((True ∧ False) → (False ∧ ((p5 → ((p2 → (True ∨ p4)) ∧ ((p4 ∨ p2) ∨ p3))) ∨ p2)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172734105191827909582415303724 : (((p3 → p2) ∨ (False ∨ ((p1 ∧ ((p5 ∧ p2) → p5)) ∨ ((p1 ∧ False) ∧ p3)))) ∨ ((p2 ∨ p1) ∨ (p2 → ((p1 ∧ (False ∧ p5)) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166274738249927995627636397417 : ((p3 ∧ (p3 → (((False ∨ (True ∧ (p2 ∨ ((p1 ∨ p4) ∨ p2)))) ∧ p5) ∨ (p3 ∧ False)))) ∨ (((p2 ∨ False) → (p2 → (p2 ∨ p2))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56721035597308910252255325369 : ((((False ∨ p4) ∨ p3) ∧ (p2 ∨ ((p1 ∧ ((p1 ∨ (True ∨ ((p2 → p5) ∧ p2))) → p3)) ∧ (False ∧ ((True ∧ (p5 ∨ p1)) ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351265935433913862709876426628 : (p4 → ((True → (p5 ∨ (False ∨ ((((p3 ∨ p5) ∧ p1) → (False ∨ ((p5 → False) ∨ ((p2 → p4) ∨ p2)))) ∧ True)))) ∨ ((p1 ∨ False) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115712380683168430974254428917 : ((((((p2 ∨ p4) → p4) → p2) ∨ p3) → ((p5 ∨ ((p1 ∨ ((False ∧ p1) ∧ p2)) ∨ (p5 ∧ (False → (True → p1))))) ∨ p3)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310520721689107911089835359376 : (p2 ∨ ((((p5 ∨ (p2 ∧ p1)) ∨ p4) ∧ p1) → ((p2 ∧ (((p5 ∧ p2) ∧ ((((True → p1) ∧ False) → p2) ∨ p2)) ∨ p2)) ∨ (p4 ∨ p1)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157438482042728776508083504590 : (((False ∨ (((p4 → ((p1 ∧ (p5 ∧ p4)) → p1)) → ((True ∧ p5) ∧ p2)) ∨ False)) ∧ (p5 ∨ p4)) ∨ (((False → p5) ∧ p3) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39653022023076528490490515582 : (((p3 ∨ ((p1 ∧ (p1 ∨ p5)) → (((False ∨ p5) ∧ (p4 ∧ ((False ∨ (p2 ∨ (p1 ∨ (p4 ∨ (p1 ∨ p1))))) ∨ p3))) ∨ True))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354598596172924663299238745269 : (p5 → ((((((((p4 ∨ (((False ∨ p5) ∧ p4) ∧ False)) ∧ (p2 → p1)) ∧ p5) ∨ True) ∨ (((False ∨ p4) ∧ True) → p1)) ∧ False) ∨ p5) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56063068091592628856746261795 : (((((p3 ∨ False) → p5) → p3) ∨ (p3 → (((p1 ∧ True) ∧ p1) ∧ ((((False → p4) → p4) → p5) ∧ (((False → p5) ∨ p2) ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660742344512242823057871598038 : ((((((((p1 ∨ p2) ∧ p4) → False) → ((((True ∨ (False → p3)) ∧ p2) ∨ (((p1 ∨ p3) ∧ p1) → p1)) ∧ p4)) → p1) → (p3 ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_207429702626086986661581905929 : (((p1 ∨ ((p3 ∨ p4) ∨ p4)) ∨ p1) → (((True → p5) ∧ ((p2 ∨ False) ∨ (p1 ∨ True))) ∨ (p2 → (p1 → (p1 → ((p3 ∨ p3) → p2)))))) := by
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
        exact h4
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h10 =>
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
          -- Implications on the right can always be decomposed.
          intro h14
          -- Implications on the right can always be decomposed.
          intro h15
          -- Implications on the right can always be decomposed.
          intro h16
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- One of the premise coincides with the conclusion.
            exact h13
          case inr h18 =>
            -- One of the premise coincides with the conclusion.
            exact h13
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- Implications on the right can always be decomposed.
          intro h21
          -- Implications on the right can always be decomposed.
          intro h22
          -- Implications on the right can always be decomposed.
          intro h23
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h24 =>
            -- One of the premise coincides with the conclusion.
            exact h20
          case inr h25 =>
            -- One of the premise coincides with the conclusion.
            exact h20
      case inr h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h27
        -- Implications on the right can always be decomposed.
        intro h28
        -- Implications on the right can always be decomposed.
        intro h29
        -- Implications on the right can always be decomposed.
        intro h30
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- One of the premise coincides with the conclusion.
          exact h27
        case inr h32 =>
          -- One of the premise coincides with the conclusion.
          exact h27
  case inr h33 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h34
    -- Implications on the right can always be decomposed.
    intro h35
    -- Implications on the right can always be decomposed.
    intro h36
    -- Implications on the right can always be decomposed.
    intro h37
    -- Disjunctions on the left can always be decomposed.
    cases h37
    case inl h38 =>
      -- One of the premise coincides with the conclusion.
      exact h34
    case inr h39 =>
      -- One of the premise coincides with the conclusion.
      exact h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328611071040511687539941857484 : (True → (((((False ∨ (p3 ∧ False)) ∧ ((p3 ∧ p2) ∨ True)) ∨ p4) ∧ (p4 ∧ p4)) ∨ (p5 ∨ (p3 ∨ (p2 → (p2 ∨ (False ∧ (p3 ∨ p1)))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160180943833453468992749137639 : (((p2 ∧ ((p3 → p5) → (p3 ∧ (((p5 → (p5 ∨ (p3 ∨ p3))) ∨ p2) → p5)))) ∧ (True → p1)) → (((p2 → False) ∨ (p1 ∨ False)) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h13 := h9 h12
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226355970711218356323263829714 : (((True → False) ∨ p1) ∨ (((p3 ∧ (p4 ∨ False)) ∨ (False ∧ (p2 ∨ p5))) ∨ (False → ((p1 ∧ True) ∨ ((p5 → p2) ∨ ((p2 → p4) ∧ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42539648542987590000955111697 : (((p1 ∨ ((True ∧ (((False ∨ p4) ∨ (p3 ∧ ((p4 ∧ p3) → ((p4 ∨ p2) ∧ (True → True))))) → p2)) ∧ (False ∨ (p5 ∨ False)))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173217011745230869261784840421 : ((p5 ∨ (p2 ∧ ((((p4 → True) → (p5 ∧ True)) → p4) → (False ∧ (p5 ∨ p4))))) ∨ ((True ∨ (p3 ∨ ((p5 ∨ p3) ∧ p5))) → (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120540354273980385001213712833 : (((((p2 ∨ (((((p2 ∧ p4) ∨ (p4 → p2)) → p1) → p4) → (False ∧ ((p1 → (p5 ∧ p1)) ∧ False)))) ∨ p5) ∨ p1) ∨ p2) → (p4 ∨ True)) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h5 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h6 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h7 =>
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
theorem thm_5_vars_53747057875812520962616446769 : ((((((p5 ∧ (p5 → (True → p3))) → p1) ∨ False) ∧ p5) ∨ (False ∧ ((p4 → ((p1 → (p3 ∨ False)) → ((p1 ∨ False) ∧ p3))) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66283032987597550539627278157 : ((p5 ∨ ((p4 ∧ True) ∧ (p5 ∧ (((p4 → p3) ∨ p2) ∧ ((False ∨ p5) ∧ (False ∧ ((((p3 ∨ p5) → p2) ∧ p2) ∨ (False ∧ p3)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216715906339233943633125601061 : ((((p5 ∧ True) → p1) ∧ p4) → (p3 → ((p1 ∧ (True → (p3 → (p4 → p3)))) → ((p1 → p5) ∨ ((p5 ∧ False) → (p4 ∨ (p3 ∧ True))))))) := by
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
  let h6 := h1.left
  let h7 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196957835070540657664140141013 : ((((p1 ∧ ((p3 ∨ p5) → False)) ∨ p1) ∨ False) ∨ ((True ∨ ((((p5 ∨ p2) ∧ (False ∨ p5)) ∨ ((p1 ∧ (p4 ∧ False)) ∧ False)) ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199318794026749974110375960014 : ((((p4 ∨ (p3 → (p1 ∧ False))) ∨ False) ∨ p2) → (p2 → ((((((p2 → p3) ∨ p4) ∧ (True ∨ p5)) ∧ (p2 → False)) ∨ (False ∨ p2)) ∨ False))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798705314338839856138751809570 : (((p1 → (((p1 → p2) ∧ (False → p4)) → ((True ∧ ((p1 ∧ ((p2 → p4) → p5)) ∧ (((p4 ∧ p5) → p5) ∨ (p5 ∨ p5)))) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260316567587311638085042271751 : ((p2 → p4) → ((p5 ∨ p2) ∨ ((((True ∨ (p3 ∨ p2)) → (p1 ∧ ((p5 → p1) ∧ (p1 ∨ p4)))) ∧ ((p3 → p4) ∧ p3)) ∨ (False ∨ True)))) := by
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
theorem thm_5_vars_49876400337632884673060908085 : ((((((p4 → ((((p2 → p1) ∧ (p1 → (False ∨ (p4 ∨ p1)))) → False) ∨ False)) ∨ False) ∨ True) ∨ p2) ∧ ((p2 ∨ False) ∨ (p4 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54648931692157698351721854365 : (((((p2 ∨ (p3 → (False ∧ True))) ∨ p5) ∨ False) → (p2 ∨ ((True → (((True ∧ p5) ∧ p5) → p2)) → (False ∨ (p2 ∧ (p3 ∧ True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252525923452506729331701816976 : ((p5 → p2) ∨ ((((p1 → p5) → (p2 → ((p2 ∨ ((True ∧ (p3 → False)) ∨ False)) → p1))) ∨ (False ∨ True)) ∧ ((False ∨ p5) → (p5 ∨ p1)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135138672812016257143759915096 : (((False ∨ (p2 ∨ (((p3 → p5) → p2) ∧ ((p1 ∧ p1) ∨ ((True ∧ (True → False)) ∨ (p2 → p2)))))) ∨ (p1 ∨ p4)) ∨ (p5 → (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144337399133879487905150744528 : (((p3 ∧ ((True ∨ (p4 → p3)) → ((((p2 ∨ True) ∨ p2) ∧ p4) ∧ (p2 ∧ (p2 → (False → p4)))))) → p4) ∧ ((False ∧ False) ∨ (True ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ (p4 → p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67761580914594751577824131535 : ((p2 → ((((((p4 → p3) → ((p3 → (p3 ∧ ((p4 → p1) ∨ p5))) → False)) ∧ (False → p1)) ∨ p1) → ((p5 ∨ p3) ∧ p1)) ∨ p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



