variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185709993143030097877576934597 : ((p2 → ((((True ∨ True) → True) ∨ p1) → ((p4 ∧ p5) ∧ p4))) ∨ ((((p2 ∧ p4) ∧ (p1 → p5)) → (p4 ∨ (p4 ∨ False))) ∨ (p3 ∧ p5))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114336387286623794165676919865 : (((p4 ∧ (p3 ∨ (((p5 ∧ (p3 ∧ p1)) → (p1 ∧ (p1 → False))) ∧ ((p5 ∨ True) ∨ p4)))) ∧ (((p3 ∧ p1) ∧ p1) ∨ True)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311049944967976303440918555436 : (p2 ∨ ((p5 ∧ p2) ∨ ((p5 ∨ (((False ∨ (True ∧ (p2 → p3))) ∨ (p2 ∨ False)) ∨ (((p2 ∧ (p3 ∧ True)) ∧ p5) ∧ (p2 ∨ p1)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165853021330989431595058712445 : ((((p5 → p5) → p4) ∨ ((((True ∧ p1) ∧ (p1 → (p2 ∨ p5))) → (False ∨ p2)) ∨ True)) ∨ (p5 ∧ (((True ∨ (p3 ∨ p2)) ∧ p2) ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809230926761539309190444480675 : (((p5 → (((False ∨ ((False ∨ (p2 → p1)) ∧ ((p4 ∧ True) ∧ ((p5 → (p2 ∨ True)) → True)))) ∨ (((False ∨ p3) ∧ p4) ∨ p4)) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_782346692725749860726501075102 : (((p3 ∨ (((((p4 ∨ p5) → (p1 ∧ False)) ∧ (p4 → ((((p2 → (False ∨ p4)) ∨ ((p1 → p2) → p5)) ∧ p3) ∨ p3))) ∧ p3) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_898641178155417373170134191908 : ((((((p4 ∨ (p1 ∧ p4)) → (p1 → (False ∨ (((True → True) ∨ p2) ∧ ((p1 → (True ∨ p3)) → p2))))) ∨ True) → ((p5 → True) ∧ False)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∨ (p1 ∧ p4)) → (p1 → (False ∨ (((True → True) ∨ p2) ∧ ((p1 → (True ∨ p3)) → p2))))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
theorem thm_5_vars_779846213752756510401306538182 : (((p2 ∨ ((p3 ∧ ((True ∨ (p2 → ((((True ∧ (p5 → (p2 ∧ p2))) ∨ ((p2 ∧ p3) → True)) ∨ p2) → p2))) ∧ (p5 ∨ True))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50429350473099101618663561151 : (((p5 ∧ ((p4 ∧ ((p2 ∧ p1) → (False ∧ (True ∧ ((False ∨ False) ∧ (p5 ∨ (p5 → p5))))))) ∧ p4)) ∨ (p5 ∨ ((p4 → p3) → True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219800400898532263100307734452 : ((p2 → (p5 ∨ (p3 ∧ False))) → ((p2 ∧ ((p5 → (((p1 ∧ False) ∨ p5) ∨ (p1 ∧ p5))) ∧ (True → True))) ∨ (p1 → (p5 ∨ (p4 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147668334085961754946065791487 : (((((((p1 → (p2 ∨ p3)) → (False ∧ (False ∧ ((p4 ∨ True) ∨ p4)))) ∨ p2) → p1) → (True → False)) → p4) ∨ (p4 ∨ ((p2 → p2) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_624149194983456960329524716074 : ((((p2 ∨ (p1 ∨ (p1 ∨ (((p5 ∨ False) ∨ p2) ∧ (((p5 → (p4 → p4)) → ((((True → p2) ∧ p1) ∨ p1) ∧ p1)) ∨ p4))))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_761430298523522664273343807155 : (((p3 ∧ ((False ∧ (((((True ∧ False) ∨ p1) → False) ∧ ((True ∨ p5) ∨ p4)) → ((False ∨ (p3 → (p5 ∨ (p5 → p5)))) → p2))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114722409796660243156115116213 : (((((p4 ∨ p4) ∨ (p5 → (((p1 ∧ p1) ∨ (p5 → p4)) → p2))) → (p2 ∨ p3)) → ((((p5 → p4) → p1) → p1) ∨ True)) ∨ (p3 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156980507619883646594696293998 : ((((p5 ∨ ((p5 → (False ∨ True)) → (p4 ∨ p4))) ∨ ((p5 ∨ ((False → p1) ∧ p4)) → p2)) ∨ False) ∨ (False ∨ (True → (True ∨ (True ∨ False))))) := by
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
theorem thm_5_vars_118643594739320285968373880587 : ((p4 ∨ ((p1 ∨ True) → (((p1 → (True ∧ p2)) ∨ p1) → (p2 ∧ (((p4 ∨ p3) → (False → ((p4 ∨ True) ∨ p3))) ∧ False))))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324536266734081116557560262014 : (p5 ∨ (((True ∨ (p5 ∧ p5)) → p3) → (True → ((p3 → p1) ∨ (p2 ∨ (False → ((True ∧ ((p1 ∧ ((False ∧ p1) ∨ True)) ∨ False)) → False))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
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
      -- False on the left can always be used.
      apply False.elim h11
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h3
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173190173412448653878714735732 : ((p4 ∨ (p2 ∨ (p2 ∨ ((((p3 ∧ (False → p2)) ∧ p5) ∨ (p2 ∨ p3)) ∨ True)))) ∨ ((True ∧ p3) ∧ ((p1 → ((p5 ∧ p1) ∧ p4)) ∧ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299498954511855355311834740282 : (False ∨ ((p4 → ((p3 ∨ True) → (((p3 ∨ p1) → (False ∧ (True → p5))) ∧ (((p5 ∧ (True → (p5 ∧ (p5 ∨ True)))) ∧ p4) ∨ p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337663696265361666534037660378 : (p1 → (((p5 → (((p3 ∨ (False ∧ p4)) ∨ p3) ∧ p5)) ∧ ((p2 ∨ (True ∧ (p1 ∧ p4))) ∧ True)) ∨ (p3 → (p4 ∨ ((p1 → p5) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157545819272801696339920044871 : ((((((p1 ∧ (True → (p2 ∨ p5))) ∨ (p2 → True)) ∨ ((p2 ∧ p5) → p4)) → p1) → (p2 ∧ True)) ∨ (((p5 ∧ p2) ∧ (p1 ∧ False)) → p2)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111036160813159383502598790515 : (((((p4 → p2) ∨ (p4 ∧ (((p3 ∨ ((p3 ∨ p4) ∨ False)) ∧ True) ∨ (p1 → p3)))) ∧ ((p2 ∧ (p5 ∨ p5)) ∨ True)) ∧ p5) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69282271588780675760262835495 : ((p5 → ((True ∨ p5) → (((p4 ∧ (False → ((p1 ∧ p3) ∧ (p5 → ((p1 → (p1 → p5)) ∨ (p4 → p1)))))) ∨ (p1 → p4)) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307506678687688460907684596188 : (p1 ∨ (True → (((((p4 ∧ p3) → True) ∨ (p2 → True)) ∧ ((p2 → p4) ∧ p1)) ∨ (p5 ∨ (((p5 ∧ (p3 → p1)) ∨ p4) ∨ (p1 ∨ True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63943025539234281838534825934 : ((False ∨ ((((p3 → p1) ∨ (p3 ∧ True)) ∨ (((p4 ∧ (p3 ∧ ((((p1 → True) → p1) ∨ p2) → (True ∧ False)))) → p5) → p4)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54501551092882644364174297000 : (((((False ∨ p5) ∧ p2) ∨ (p1 ∧ (p4 ∧ p3))) ∨ (True ∧ (False → (((False → p3) → (True ∨ (p1 ∧ (p2 → (True ∨ p5))))) ∨ p5)))) ∨ p4) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141955053128018224958677011588 : (((True ∨ p1) → (((p2 → (p5 ∨ (True → (p4 ∨ (p4 ∧ (p5 ∧ (((False ∧ p1) → p5) ∨ False))))))) → True) ∧ p4)) → ((True ∨ p1) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57894219914653158596904827684 : (((p3 ∨ (False ∨ True)) → ((((p2 → (True → False)) ∨ p5) → p5) → (((True → p5) ∧ (((False ∧ p2) ∧ True) → p1)) ∨ (False ∨ True)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61501928207694305203507915665 : ((p1 ∧ (((p5 ∨ (p1 ∧ ((p3 → (((p2 ∨ p4) → True) ∧ True)) ∨ p2))) → ((p2 ∧ p4) ∨ p1)) ∧ ((True ∨ (p2 → p2)) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230462832007602125532884234993 : (((p5 ∨ p2) ∧ p3) → (p5 → ((((p5 ∨ True) ∧ p1) → False) ∨ (p3 ∧ (p1 ∨ (False → (((((p5 ∨ p1) ∧ p5) → p3) → True) ∧ p5))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148238130356156887600123306419 : (((((((True ∧ False) ∨ p2) ∧ (p1 ∨ (p2 ∧ p3))) ∧ False) ∨ (p5 ∧ (p5 ∧ p2))) ∨ ((p1 ∨ True) ∧ True)) ∨ (p2 ∨ ((p3 ∧ True) ∨ p3))) := by
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
theorem thm_5_vars_57451447865766731686906380335 : (((p5 ∨ (p3 ∧ p1)) ∨ (p2 → (((p1 ∨ (((p5 → p3) ∨ (True → ((p2 → p5) ∧ ((p4 ∨ False) ∧ p1)))) → p2)) ∧ p2) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166328771232992279975841337343 : ((p5 ∧ ((p5 ∧ p5) ∧ ((p4 ∧ ((p2 ∧ ((True ∧ p1) ∨ p2)) ∧ p1)) ∨ (p4 → True)))) ∨ ((False → ((True ∨ p4) ∧ (p5 → p4))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232679042783148785444335143910 : ((p1 ∧ (p4 ∧ p4)) → (p3 ∨ ((((p5 ∨ (((False ∨ ((((p3 ∨ p2) ∧ p4) → False) ∧ p1)) → False) ∧ (p3 ∨ True))) ∧ p5) ∨ p1) ∨ p4))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64610725226666080931483951272 : ((p1 ∨ ((p1 → p3) → (True → (((p1 → p5) ∧ ((p2 ∧ (p4 ∧ ((p5 ∨ (False ∨ p3)) ∧ p4))) ∨ (p5 → p3))) ∨ (p2 ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184146612478862388783066446570 : (((False ∨ ((((p4 ∨ p1) ∨ (True → p4)) ∨ p5) ∧ p1)) ∨ p4) ∨ ((False → ((((True → True) → True) ∨ (p2 → (p1 → p5))) ∧ p5)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_53923378070248019779233124096 : (((p3 ∨ ((p1 ∧ (p5 → (p4 ∧ p4))) → (p3 ∧ p5))) ∨ (((((p1 ∨ p3) ∨ True) ∧ True) ∨ False) ∨ (p3 ∧ (p3 ∨ (p4 → p3))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166281077876618560586330745799 : ((p4 ∧ (((p1 ∧ p2) ∧ (((((p3 ∧ False) → True) → p5) ∧ (p3 → p5)) ∧ p3)) ∨ True)) ∨ (p3 ∨ ((False ∧ False) → ((p1 ∧ p3) ∨ p2)))) := by
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
theorem thm_5_vars_344320398582960236920926881455 : (p2 → (p3 ∨ ((p5 ∧ p4) ∨ (((p4 ∨ (True ∨ p3)) → (((False ∧ ((((p3 → p3) ∧ (p3 ∨ p3)) ∧ False) → p3)) ∧ p2) ∧ False)) ∨ p2)))) := by
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
theorem thm_5_vars_444188613916411773218917932328 : ((((True ∧ (((((p3 ∧ p4) ∧ (p5 ∧ ((p3 ∧ p1) ∨ p1))) ∧ False) ∨ p1) ∨ ((False ∨ p4) → (p1 → True)))) ∨ (p3 → (p5 ∨ p4))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135054838189010920770655426424 : ((((((p5 ∧ ((((p1 → p2) ∨ False) ∧ (True ∨ (True ∨ p1))) ∧ False)) → (p3 → p5)) ∧ p2) → p5) ∨ (p2 → True)) ∨ ((p3 → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217030767988598645278808204454 : ((((True ∨ p4) ∧ p1) ∨ p1) → (p4 ∨ ((((((p1 ∧ p4) ∨ p3) → (p3 ∨ p1)) → (p4 → p5)) ∨ p1) → (p3 ∨ ((p3 ∨ True) ∨ True))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160887944046131107660877393902 : ((((p4 ∨ p3) ∧ (False → False)) ∨ (((p4 → p4) ∨ (False ∨ ((p4 ∧ (False → p1)) ∧ True))) → p4)) → (((p4 ∨ p3) ∧ (False → p5)) ∨ p5)) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : ((p4 → p4) ∨ (False ∨ ((p4 ∧ (False → p1)) ∧ True))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h12 := h9 h10
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219695684242302988499095188719 : ((p1 → ((False ∨ True) ∨ p2)) → (((p3 ∧ p4) ∧ p2) ∨ ((p4 → False) ∨ (p3 → ((False → p5) ∨ (False ∧ (p3 ∧ (p5 ∨ (p5 ∨ True))))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165655022782274706958030999151 : ((((p2 → (False → (p4 → p5))) → p1) ∨ ((p3 → ((p2 ∨ p2) ∧ (p3 → p3))) ∧ p3)) ∨ (((p2 ∧ (p5 ∧ p5)) → (p4 → p4)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245100957698525921763681564066 : ((p2 ∧ True) ∨ (((p1 ∧ (p1 ∧ (False ∧ (False → (True ∨ p1))))) ∧ ((p4 ∨ ((p1 → (True → False)) ∨ (p2 ∨ True))) → (p4 ∨ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196819523641451879601810092140 : (((False ∧ ((p4 ∨ p2) ∧ (p1 ∨ p2))) ∧ p4) ∨ (((p1 ∧ (p4 ∧ p4)) ∧ (p5 → p5)) → ((p1 → p2) → ((False → (p5 ∨ True)) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739150232880942608142590220894 : ((((p4 ∧ True) ∨ (((((p2 ∨ p5) → p1) ∨ False) → p4) ∨ (((p1 ∧ p4) ∧ (((False → False) ∨ p2) → False)) → ((p4 ∧ p2) → True)))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149529865092232764584530765351 : ((p1 ∧ (p3 → ((True ∨ (((p4 → p4) → (((((p3 ∧ p2) → p4) ∧ p2) ∧ p1) ∨ p4)) → p1)) → p1))) ∨ (True ∧ ((p3 → p2) → True))) := by
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
theorem thm_5_vars_83354284209957084308325312712 : ((((p3 → p2) ∧ (((((((True ∧ p3) ∧ False) → p5) ∨ p2) → (p2 ∧ p4)) ∨ True) → False)) ∧ ((p1 ∧ p2) → (p2 ∧ (p3 ∧ p1)))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((((((True ∧ p3) ∧ False) → p5) ∨ p2) → (p2 ∧ p4)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134111153628388934996410228579 : (((((True ∧ (False ∨ p1)) ∨ (((p3 ∨ ((p1 ∧ p4) ∧ (p3 → p2))) → p5) ∨ (p4 ∨ p5))) ∧ (p2 → True)) ∨ p2) ∨ ((False → True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111478370213714536123334332896 : (((p2 → (((((p4 ∧ ((p2 ∨ p5) → (((((p2 ∧ p1) ∨ p5) ∧ p1) → p1) ∨ p1))) ∧ False) ∨ p3) ∧ p5) ∧ p2)) ∧ True) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693122803048351587167724836221 : ((((p3 ∧ (p5 → ((((False ∧ False) ∧ (p1 ∨ p1)) → (p2 ∧ p1)) → p3))) ∧ ((True ∨ (((p5 → (p3 ∧ True)) ∧ p2) → True)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53362822012554595937687405065 : (((((True ∧ False) ∨ (p4 ∨ ((True → p4) ∨ (p4 ∨ True)))) ∨ p5) → ((((p3 ∨ (False ∧ (p2 ∨ False))) → p5) ∧ p1) → (p2 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241290409606698458029765627207 : ((False → True) ∧ (((p2 → p1) ∧ ((((((p5 → True) ∧ False) ∨ ((p2 ∨ False) ∨ p5)) → p2) ∧ (p4 ∨ True)) → p4)) → (p1 ∨ (p1 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233929996354684642341397868121 : ((p4 ∨ (p3 → p1)) → (((((p4 → p1) → False) → (False ∧ ((((p4 → False) ∧ False) → p2) ∧ (True ∨ p2)))) → ((p5 ∧ False) ∧ p3)) ∨ True)) := by
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
theorem thm_5_vars_232046247243495588071194216827 : (((p3 ∨ p4) → p1) → ((((((True ∨ True) ∨ ((True ∧ ((p1 ∧ p2) → p5)) ∧ p3)) → False) ∨ ((True → p5) → True)) → (p5 → p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62461271260050941416486667655 : ((p3 ∧ ((p5 ∨ True) ∧ (p1 → ((False ∧ ((p3 ∧ False) ∨ (p3 → (p1 ∧ (p2 ∨ (((p1 → p2) ∨ p2) ∧ True)))))) ∧ (p2 ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178403681380305156235041211091 : ((((p1 ∧ p1) ∨ (((p1 ∧ (p2 → True)) → p2) ∨ p3)) → (p2 → p3)) ∨ (((((p2 → p3) ∧ p5) → (p5 → (False ∧ p4))) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126095144107243563243839774675 : ((True ∧ ((((((p3 → p4) ∨ (False → (((p5 ∧ True) ∧ True) ∧ p1))) ∧ p1) ∨ ((False → (p3 → p4)) → True)) → p1) → p1)) → (p5 ∨ True)) := by
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
theorem thm_5_vars_683785602425679078024470822583 : ((((((((((p5 ∨ True) ∧ p5) ∨ p1) ∨ p4) → (False ∧ (p4 ∨ True))) ∧ (p5 → False)) ∨ p2) ∨ (p2 ∧ (True → ((p4 ∨ p4) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726015098887048233061534933253 : (((((p5 → p3) ∧ p2) ∨ ((p4 ∧ (((True ∨ ((((p5 → (p1 ∨ False)) ∨ p5) → p3) ∨ p4)) ∧ True) → p5)) ∧ (p3 → (True → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60279617586977185593796066985 : (((False → p5) → ((((((True → p3) → p4) ∨ (p4 → p5)) → p2) → (p2 → ((True ∧ p5) ∧ (True ∨ p1)))) ∧ ((False → p4) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616431345582857447297041601557 : (((((((False → p3) ∧ (p3 ∨ ((p1 ∨ p3) ∨ False))) ∧ (p4 → p5)) → (p1 → ((((p4 ∨ (p2 ∧ True)) ∨ True) ∨ False) ∨ p2))) ∨ p3) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56628177487754548365995750095 : ((((p3 ∧ p2) ∧ p4) ∧ ((p4 → (((((p5 ∨ False) ∧ (p5 ∨ p3)) ∨ p1) ∧ True) → ((p3 ∧ (False → p4)) ∧ p4))) ∨ (p2 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244616156614161305243153013459 : ((False ∧ p5) ∨ (((p5 ∧ p2) → (((((p2 ∨ (False → False)) → p4) ∧ ((p5 ∨ p4) ∨ p4)) → (p1 → p3)) → ((True ∨ p1) ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53858012946411981291063778338 : ((((p2 ∨ (True ∧ p3)) ∨ ((p4 ∧ True) ∨ (p3 ∨ False))) ∨ ((((False ∨ True) → p5) ∧ (p4 → ((False ∧ (p2 ∧ p1)) → p2))) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358539603212077667738499742049 : (p5 → (p2 → ((((p5 ∨ ((False ∨ (p3 ∧ (p4 → False))) ∨ p1)) ∧ True) → (p3 ∨ (p4 ∧ p1))) ∨ ((True ∧ (p5 → False)) → (True ∧ False))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41020677550935595148130973751 : (((((((p3 ∨ False) ∨ (True ∨ (p3 → (p4 → p5)))) ∧ ((False → (p3 ∨ p5)) ∧ (p2 ∨ (True → False)))) → False) → (p2 ∧ p1)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632720162866833001429931801178 : (((((p5 → (((False ∨ p4) → (False ∨ (True → p2))) → (p2 ∨ ((((p3 ∨ ((p5 → p1) ∧ True)) ∨ True) ∨ False) ∧ p3)))) → p2) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776269676258933822870775085964 : (((p1 ∨ ((((p2 ∨ p5) ∧ False) ∧ (p1 ∧ (True ∧ ((p5 ∧ ((p4 ∧ (p3 ∧ (True ∨ (p3 ∧ False)))) → p4)) → (p1 ∨ p4))))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45514762054524189390785846514 : (((p1 ∨ ((p4 ∧ (((p5 ∧ p1) ∨ False) → (((p2 ∧ p5) → (True → (p3 → False))) ∨ (p1 → (p1 → p4))))) → (p4 ∧ p2))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350292824525047677279367697392 : (p4 → ((p1 ∨ ((((p5 → p4) → (p1 → ((((((True ∨ (True ∧ p5)) ∨ p2) ∧ (p1 ∨ p3)) ∧ True) ∨ False) → p3))) ∧ True) ∨ p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352641479409129139544344460238 : (p4 → ((p2 ∧ p3) ∨ ((((False ∧ ((p4 ∧ (p1 ∧ p2)) ∨ (True ∧ p1))) → (p1 ∧ p5)) → (p3 ∧ (False ∧ False))) → (False ∨ (True → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∧ ((p4 ∧ (p1 ∧ p2)) ∨ (True ∧ p1))) → (p1 ∧ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
    -- Conjunctions on the left can always be decomposed.
    let h7 := h4.left
    let h8 := h4.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h3
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257986416232382300389642741274 : ((p4 ∨ p1) → (((False ∧ ((p3 ∧ (p1 ∧ p1)) → p5)) ∨ (((True → (p1 → p4)) ∧ p5) → (True ∧ ((True ∨ False) ∧ p1)))) ∨ (p4 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h7 := h4.left
    let h8 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596956982613409078870587939421 : (((((p4 → ((p2 ∧ (True → p3)) ∨ p3)) ∨ ((p1 ∧ (p4 ∨ ((p2 ∧ (((p1 → (p5 ∧ p4)) ∨ p2) → p1)) ∨ p3))) → False)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113191427501522605403780874808 : ((((True ∧ (True ∧ (((True ∨ (((p4 ∨ False) → False) ∧ (p3 → p5))) ∨ (p4 → (p5 → p1))) → p4))) ∧ False) ∧ (True → p1)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136739406992382044321095847240 : (((False ∨ False) ∧ (((((p3 ∧ p5) → (p4 → p5)) ∨ (p4 ∧ False)) → (p4 ∨ ((p3 ∧ False) ∧ p4))) ∧ (p4 ∧ p5))) ∨ (p5 ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147031789418436540770840364861 : ((((p3 → (p4 ∧ (((p2 ∧ p1) → (p1 ∧ p2)) → ((p2 ∧ p2) ∧ p2)))) ∨ (p5 → (False ∧ p4))) ∧ p5) ∨ ((True ∨ p1) ∨ (True ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41529597680655599290944403469 : ((((p2 → (p5 → ((p3 → (p2 → (p4 ∨ p2))) ∨ p1))) ∧ ((p2 → (False ∨ (True ∨ p3))) → (p5 ∨ ((True ∧ False) ∧ True)))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671623492870434557621285524974 : ((((((((((p1 ∧ ((p3 → p1) → (True ∧ True))) → p2) → (p4 ∧ p4)) → p5) ∧ (True ∧ p2)) ∧ p5) ∧ p4) → ((True → p1) → p1)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h11
  -- One of the premise coincides with the conclusion.
  exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699753458489681332805672179345 : (((((p5 → ((p2 ∧ ((p5 ∨ True) ∧ False)) ∧ p2)) ∧ (p1 ∨ True)) → ((p1 ∧ (p4 → ((p5 → p3) ∧ (p1 ∨ p4)))) ∧ (p5 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118536496621726585148742848251 : ((p3 ∨ (p4 ∧ (p2 ∨ ((p1 → ((p3 → p4) ∨ ((((True ∨ p1) ∧ p4) → True) ∧ (((True ∨ p4) ∧ p4) → p2)))) → p2)))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_554099778586730638356231506460 : (((p2 ∨ ((p4 ∨ (((p3 → (p2 ∧ p3)) ∨ p2) ∨ (False → p5))) → ((p3 → False) ∨ ((False ∧ (p2 ∧ p4)) → ((False ∨ p4) ∧ p3))))) ∧ True) ∧ True) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- False on the left can always be used.
        apply False.elim h12
        -- Conjunctions on the left can always be decomposed.
        let h14 := h11.left
        let h15 := h11.right
        -- False on the left can always be used.
        apply False.elim h14
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- False on the left can always be used.
        apply False.elim h18
        -- Conjunctions on the left can always be decomposed.
        let h20 := h17.left
        let h21 := h17.right
        -- False on the left can always be used.
        apply False.elim h20
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- False on the left can always be used.
      apply False.elim h24
      -- Conjunctions on the left can always be decomposed.
      let h26 := h23.left
      let h27 := h23.right
      -- False on the left can always be used.
      apply False.elim h26
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10382904859334443038799609385 : (((True → (((p4 ∧ p4) ∧ (True ∨ p3)) ∧ ((False ∨ (p2 ∨ (True ∨ ((p4 ∧ (p4 ∧ ((False ∨ False) → True))) ∨ p3)))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66850689806881867035604961674 : ((True → (p4 → (p2 → ((((((False ∨ p4) ∨ p1) ∧ (p4 ∨ (((p5 → (p1 ∧ p1)) ∧ (p3 ∧ p3)) ∨ p3))) ∨ p4) ∧ p5) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165348747078562930243123204623 : ((((True → p5) ∨ (p4 ∧ ((((p4 ∨ False) → True) ∨ False) ∧ p2))) ∧ (p4 ∧ (p5 → False))) ∨ ((p3 → (p1 → ((p2 ∧ False) ∨ p3))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188729625304897641488729843117 : ((((True ∨ (p3 → p5)) ∨ (True → False)) → (p3 ∨ True)) ∧ ((True → (p3 ∨ (p4 → p5))) ∨ (p3 → ((p5 ∧ p5) ∨ (p5 ∨ (p1 ∨ p3)))))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153754465090365233788420315071 : ((p4 → ((True ∨ (((p3 ∧ p4) ∧ ((True → False) → (p4 ∨ True))) ∨ (((True ∨ p2) → p1) ∨ p1))) ∧ p3)) → ((p1 ∧ (p2 ∧ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231501111565895491415400984973 : (((p3 → p5) ∨ p1) → ((((p1 ∧ False) → (False → False)) → (p1 → (p4 → p1))) → (((p5 ∨ True) ∧ (False → p3)) ∨ (True → (p5 ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617305785376716024758412903863 : ((((((((False → p1) ∨ (p2 → False)) → p4) ∨ p5) → ((p5 → (p4 → False)) → ((p2 ∨ p2) → ((p3 ∧ p3) ∧ (True ∧ p3))))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_988540746385069069416854134638 : (((p3 ∧ ((p1 ∨ ((p4 ∨ p1) ∨ ((((p1 ∧ (p4 ∧ p3)) ∨ (p2 → (p5 ∨ (True ∨ True)))) ∨ ((True ∨ False) ∧ p4)) ∨ p2))) → False)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p1 ∨ ((p4 ∨ p1) ∨ ((((p1 ∧ (p4 ∧ p3)) ∨ (p2 → (p5 ∨ (True ∨ True)))) ∨ ((True ∨ False) ∧ p4)) ∨ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614183704896703049480915269580 : ((((((p3 ∧ (p4 ∨ ((p5 ∨ ((p4 → p3) → ((p3 ∨ (True ∧ (p2 ∧ True))) → p2))) ∨ p1))) ∨ p3) → (False ∨ (p2 ∨ False))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_678252211802605127281729365853 : (((((p5 ∨ (p2 → (((p5 ∨ p1) ∧ p2) ∨ (p5 ∨ p4)))) → (((p2 → False) ∧ False) ∨ (True ∧ False))) ∨ (((p5 ∧ True) ∨ p5) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204204062770840327103624505601 : (((((p1 ∧ False) → False) → p5) ∧ p2) ∨ (p2 ∨ ((p2 ∧ p4) ∨ ((((p2 → ((p1 → p1) ∧ True)) ∨ (p4 → False)) → False) → (p1 ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213151648503890041020501049646 : ((((False ∧ p5) ∨ True) ∧ p2) ∨ ((True → (p2 → p4)) ∨ ((p4 → (p2 ∨ ((p5 ∨ True) ∨ ((p4 ∨ (p1 → p1)) ∧ (True ∧ p5))))) ∨ False))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342591857591597020424339606937 : (p2 → (((p4 ∧ ((((p2 ∨ False) ∨ p3) → (p1 ∧ False)) ∧ p1)) ∧ p1) → ((p4 → p5) ∧ (((p5 ∨ True) ∨ p4) ∨ (p3 ∧ (False → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : ((p2 ∨ False) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h11 := h8 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h2.left
  let h14 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h13.left
  let h16 := h13.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h16.left
  let h18 := h16.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304128457147788969509835488379 : (p1 ∨ ((p5 → (p2 ∨ ((p2 ∧ ((((p1 → False) ∨ ((p2 ∨ (p4 → p2)) ∧ (p2 ∧ p4))) ∨ (p3 ∧ p2)) ∨ (p1 → False))) ∨ True))) ∨ p2)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44780529755378347601180252953 : ((((True → (p3 ∧ (p4 ∨ p2))) → (p5 ∨ (p5 → (p2 ∨ ((p2 → False) → (((p2 → (p5 → p1)) ∧ False) ∨ (p2 ∨ p3))))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180928530029949953869141014331 : (((p2 ∧ p5) ∧ ((p2 → (p3 ∨ (p1 ∨ p1))) ∨ (p5 ∨ (p5 → p2)))) → (((True → p5) → (((p4 ∧ False) ∧ p3) ∧ (p3 ∨ p5))) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (True → p5) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h8
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h16 : (True → p5) := by
        -- Implications on the right can always be decomposed.
        intro h17
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h16
      -- We need to get the left conjuct of h18 based on <expert-advice>.
      let h19 := h18.left
      -- We need to get the left conjuct of h19 based on <expert-advice>.
      let h20 := h19.left
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h23 : (True → p5) := by
        -- Implications on the right can always be decomposed.
        intro h24
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h25 := h2 h23
      -- We need to get the left conjuct of h25 based on <expert-advice>.
      let h26 := h25.left
      -- We need to get the left conjuct of h26 based on <expert-advice>.
      let h27 := h26.left
      -- We need to get the right conjuct of h27 based on <expert-advice>.
      let h28 := h27.right
      -- False on the left can always be used.
      apply False.elim h28



