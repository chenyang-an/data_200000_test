variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148869748172312680777658742404 : (((((p3 ∨ p2) ∧ p2) ∧ p3) ∨ ((p3 ∧ (p2 → (True ∨ (p3 ∧ (((p1 ∨ p4) ∧ p3) → False))))) ∧ False)) ∨ (((True → p4) ∨ True) ∧ True)) := by
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
theorem thm_5_vars_226864288901448214183144629022 : (((p5 ∧ True) → p4) ∨ (((((p2 ∧ ((p5 → (p1 → p1)) ∧ (p2 → True))) ∧ (p5 → ((p3 ∨ p5) ∧ p3))) ∨ p3) ∨ p5) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56097945470785992870219841910 : ((((p1 ∨ p1) ∧ (p1 ∨ p4)) ∨ (p3 → (((True ∧ (p5 ∧ (p3 ∧ ((((p4 ∨ p1) ∧ p3) ∨ False) ∧ (p4 ∨ False))))) ∨ True) ∨ True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246572660480434586175662035712 : ((p5 ∧ p2) ∨ (((p1 ∨ (((((True ∨ True) → p2) ∨ ((p1 ∨ p3) → p3)) → ((p5 → True) ∨ p1)) → True)) → p3) ∨ (p5 → (True ∨ p5)))) := by
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
theorem thm_5_vars_186593196567153438675894820657 : ((((p4 ∨ (p5 → (p1 → (True ∧ p4)))) ∨ p3) → (p4 → p1)) → (True → (p1 → ((((p3 → False) ∧ True) ∧ p3) → (p3 → (p5 ∧ p5)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h11 := h8 h10
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h4.left
  let h13 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
  have h16 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h14, we can now drive its conclusion.
  let h17 := h14 h16
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47129108352968627806332275340 : (((((False → (p2 ∧ p4)) ∨ (((True → ((True ∧ ((p3 ∧ p5) ∨ p1)) ∨ p5)) ∧ False) → p5)) → ((True → p2) → p3)) ∨ (True → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261229396040941389084581130029 : ((p4 → p5) → ((p2 → p3) → (((True → ((((False ∨ p1) ∧ p4) ∧ False) ∧ p3)) → (((True ∨ p1) → (p2 → (False ∧ p4))) ∧ p4)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h12
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- False on the left can always be used.
    apply False.elim h15
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h16 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h18 := h3 h17
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- False on the left can always be used.
    apply False.elim h20
  case inr h21 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h22 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h23 := h3 h22
    -- We need to get the left conjuct of h23 based on <expert-advice>.
    let h24 := h23.left
    -- We need to get the right conjuct of h24 based on <expert-advice>.
    let h25 := h24.right
    -- False on the left can always be used.
    apply False.elim h25
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h26 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h27 := h3 h26
  -- We need to get the left conjuct of h27 based on <expert-advice>.
  let h28 := h27.left
  -- We need to get the right conjuct of h28 based on <expert-advice>.
  let h29 := h28.right
  -- False on the left can always be used.
  apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261634250581702249846553728233 : ((p5 → p5) → ((p4 → (((p3 ∨ p5) → (True → (False → ((p5 ∨ ((p3 → p5) ∧ p5)) ∧ (p3 ∧ p2))))) → p5)) ∨ (p1 → (True ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685937016605364480548343654413 : (((((((False → ((False → False) → p1)) → (p3 ∧ p3)) ∧ (p2 ∨ (True → p1))) ∧ (p5 → p1)) → ((p3 ∧ (p5 → True)) ∨ (True ∨ p4))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208862693526737277669874414574 : ((p4 ∧ (((p1 → False) ∨ p5) → p3)) → (((p5 ∨ ((p3 ∨ (p4 → p2)) ∧ p4)) ∧ ((((p2 → p4) ∧ (False ∧ p5)) ∧ p2) → True)) ∨ True)) := by
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
theorem thm_5_vars_4527760053708106419062463946 : (p3 → ((True ∧ (p1 → ((True ∧ ((False ∨ (False ∨ (p2 ∧ ((True ∨ p5) ∧ p2)))) → p1)) → p5))) ∨ ((p3 → p4) ∨ (True ∨ p4)))) := by
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
theorem thm_5_vars_319056523664077277506239437444 : (p4 ∨ ((True ∧ (((((False ∧ (p5 ∨ p1)) ∧ p2) ∨ (p3 → p2)) ∨ p2) ∧ ((p4 ∧ p5) ∧ (True → p2)))) ∨ (((True → True) ∨ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126900739214624293490697431908 : ((True ∨ ((((p4 ∧ (((p4 ∨ p2) → False) ∨ p3)) ∧ (((True → p1) ∨ p1) → ((p1 ∨ p3) → True))) ∨ (p4 ∨ p1)) ∧ p4)) → (p1 ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608431662486719639887041761570 : ((((((((True ∧ p4) ∧ (((False ∧ p4) → p3) ∨ (p2 → ((((p1 ∧ p2) ∨ (p5 ∨ False)) → p5) ∧ True)))) ∨ p2) → p2) ∨ p2) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_341675981934334705429312214458 : (p2 → (((False ∧ ((p4 ∧ (p1 → ((((p4 ∧ p2) ∧ (p3 ∧ p4)) ∧ True) ∧ False))) ∨ (p2 ∧ (p4 → (p5 ∨ False))))) ∨ p2) ∨ (False ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42378453776994122317615168638 : (((p4 ∧ ((p1 → (p3 ∧ ((((((p2 → (p4 ∧ (True ∨ False))) → p3) ∧ False) ∧ (p1 → (p4 ∨ False))) → p3) → p3))) → p2)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807975927996791116394727105154 : (((p4 → ((p3 ∨ False) → (((p4 → ((True ∧ p3) ∧ (p2 ∨ ((p4 → p5) → False)))) ∧ p3) → (((p2 → (p1 → True)) → p1) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77017494546861801146589612780 : (((((p5 ∨ True) → (True ∧ (p4 ∨ p1))) ∨ ((((True ∨ (p5 ∧ (p3 → False))) ∨ True) ∨ p4) ∨ (p4 ∨ ((True → p2) ∨ p3)))) → p3) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ True) → (True ∧ (p4 ∨ p1))) ∨ ((((True ∨ (p5 ∧ (p3 → False))) ∨ True) ∨ p4) ∨ (p4 ∨ ((True → p2) ∨ p3)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657684142349681047551617662674 : (((((True → p5) → (False ∧ ((False ∧ (p1 ∨ (p5 ∨ ((p1 ∨ (False ∨ ((p3 → p3) ∧ p1))) → p3)))) ∧ (p3 ∧ p2)))) ∨ (False → p1)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179634634075692477925239572142 : ((p4 → (False ∧ ((((p5 ∨ p5) ∨ p1) ∨ (True ∧ (p1 → p3))) → p5))) ∨ ((p3 → ((((False → (p5 ∨ p3)) → p5) ∧ p4) → False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219550796030145087762399839764 : ((True → ((p4 ∧ True) ∧ True)) → ((p1 → (((p3 ∨ (p2 ∧ (p2 ∧ ((p2 ∨ p3) ∨ False)))) ∧ True) ∨ (((p5 ∨ p3) → p5) ∧ p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230453891801749831396866302821 : (((p5 ∨ p1) ∧ True) → (p2 ∨ (p3 ∨ (((False ∨ ((p5 ∨ p2) → ((False ∧ p4) ∨ p2))) → False) → ((p2 ∧ p1) ∨ ((False → p2) ∨ True)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
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
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47553320232859686084972976071 : (((True → (((((p5 ∨ (p4 ∨ False)) ∧ p4) ∧ p3) ∧ (p5 ∨ ((p3 → (p3 ∧ p5)) ∨ p1))) ∧ ((p1 ∨ p1) → p4))) ∨ (p4 → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133837599309487855620094927202 : ((((p5 ∨ p2) → ((False ∧ (p2 ∨ p4)) ∧ (p4 → (((p4 ∨ ((p2 → (p5 → p3)) ∧ p4)) → p3) ∧ False)))) ∧ True) ∨ (True → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115767296886810155860795251821 : (((True → ((False ∨ (False ∨ p4)) ∧ p5)) → ((p4 ∨ p3) ∨ (((((p2 ∨ p5) ∨ False) ∧ ((False ∨ p1) ∧ p1)) ∨ False) → p2))) ∨ (p3 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_913422676790711549705566180802 : ((((False ∨ (((p1 ∨ False) ∨ (((True ∧ (True ∨ (p4 ∧ p4))) → (False ∨ False)) → p4)) ∨ p3)) → (True ∧ ((p2 → (p1 → True)) → p5))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ (((p1 ∨ False) ∨ (((True ∧ (True ∨ (p4 ∧ p4))) → (False ∨ False)) → p4)) ∨ p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (True ∧ (True ∨ (p4 ∧ p4))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
      -- False on the left can always be used.
      apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : (p2 → (p1 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h13 := h9 h10
  -- One of the premise coincides with the conclusion.
  exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52788719728139821833724895256 : (((((p4 → (p5 → p1)) ∧ (p2 ∧ ((True ∨ p3) ∧ p1))) → (False → p3)) → (True ∧ (p3 ∧ (p4 ∨ ((p2 → (True → p2)) → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303915290093584906171513037323 : (p1 ∨ ((((p1 ∨ (p1 ∧ (p4 → p5))) → ((p2 ∧ (p2 ∨ p2)) ∨ True)) → (p5 ∧ (p5 ∨ (((p5 → p5) → p4) → (False → p2))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753178081070225342055563927090 : (((False ∧ (((p3 ∨ p2) ∨ (((((p3 ∨ (p4 → p1)) ∨ (True → ((True → True) ∨ False))) ∧ (p1 ∨ p2)) ∨ True) ∧ p2)) ∧ (False ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263588374016364680014263289655 : (True ∧ ((p5 ∨ ((p3 ∨ p2) ∨ (p1 ∧ ((p3 ∧ (p5 ∧ (p2 → True))) ∨ (p5 → ((False → False) → p3)))))) ∨ (((p3 ∨ p4) ∧ False) → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_612901490861141642980565760378 : (((((p1 ∨ (p5 → (((((((p2 ∨ (p3 → p1)) → p3) → p3) ∧ p4) → False) ∨ p5) ∨ (p4 ∧ (True ∨ p3))))) ∨ (p2 ∧ p4)) ∨ p3) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133846067936256314303283173130 : (((True ∧ ((p3 ∨ False) ∧ ((p2 → ((p2 ∧ (p1 → p3)) ∨ p4)) ∨ (True ∧ (((p4 ∨ True) ∧ p5) → p1))))) ∧ False) ∨ (False → (True ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58100881160145478959500570787 : (((p1 ∧ p2) ∧ (p5 ∨ (p2 → ((((False → p2) ∨ p4) ∧ False) ∧ (((((p1 ∧ (True ∨ (p1 ∧ True))) → p5) → p1) ∨ p4) ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178552584980465986196743957827 : (((((p1 ∨ (False ∧ p1)) ∧ p3) ∨ p2) ∧ (True ∨ (False → (False ∧ p1)))) ∨ ((p3 → ((((p3 ∨ p2) → p5) ∨ p2) → p1)) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266010770526370476265611916273 : (True ∧ (p1 → ((False ∨ (((True ∧ (p3 → ((p5 → ((p1 → (False ∧ p4)) ∧ ((p3 → p3) → True))) → False))) ∧ p4) ∧ True)) ∨ (p1 → p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637193579183555897628458822447 : (((((p3 ∨ (True ∧ (p1 → ((False → p4) ∨ ((p1 → p4) ∨ p5))))) ∨ ((((p3 ∨ False) → False) → ((True ∧ p5) ∧ p2)) ∧ p3)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58414763424044003439861438320 : (((p2 ∨ p2) ∧ (True ∧ (((p5 ∨ True) ∧ (((p3 → p3) → (False ∨ (False ∨ False))) ∧ False)) ∧ (p1 ∧ (((p3 → p4) → p4) → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709661770981704990766821992201 : ((((p4 ∨ (((p4 ∧ False) ∧ (p1 ∨ True)) → p4)) → ((p1 ∨ ((p1 ∨ p4) → (p5 ∧ p3))) ∨ (True ∧ ((p1 → p1) ∨ (p3 ∧ p4))))) ∨ p3) ∧ True) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111763851660865766561857368207 : ((((((p5 ∨ (p4 ∧ (((p5 ∨ True) → True) → p3))) → p3) ∧ (p5 ∧ ((p4 → (p5 ∧ False)) ∨ p2))) ∧ (p5 ∨ False)) ∨ False) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731486244478825373457189480147 : ((((True → (p1 → p4)) → ((p3 → (p2 ∧ (((p2 ∧ (p5 ∧ (((p4 ∧ (p3 ∧ False)) ∨ (p4 ∧ False)) → True))) ∧ p3) ∧ p2))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196157319022565473315538227656 : ((True ∨ (p3 → (((p1 ∧ False) → p2) → True))) ∧ (((p4 ∨ p4) ∧ (p4 ∨ True)) → ((True → (p4 → (False ∨ (False ∨ p5)))) ∨ (p3 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50987125838054580677721330427 : ((((False ∧ p5) ∧ (p1 ∨ (False ∨ (True ∨ (((p2 → False) ∧ (p1 ∨ p3)) ∨ (p1 ∧ p4)))))) ∧ ((p5 → ((p1 ∧ p4) → p1)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56727635425664066919151604088 : ((((p2 ∨ p3) ∨ False) ∧ (p4 ∨ ((((p1 → p1) ∧ (False ∧ (p2 ∨ p1))) ∨ (p5 ∨ p3)) → (p3 ∨ (False → ((p5 ∨ True) ∨ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740451961753607778113366164223 : ((((p1 ∨ p4) ∨ (((p5 → True) → False) ∨ (((p5 ∧ (((p4 ∨ p2) → False) ∧ p3)) → (p3 ∨ p3)) ∨ ((True ∧ (p5 ∧ p5)) → p5)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41009180912134428285742519086 : (((((True → (((p4 ∨ ((((False ∨ p4) ∧ p4) ∧ (p3 ∨ (p2 → p1))) ∨ True)) → p4) ∨ (p5 ∨ p5))) ∧ p5) → (p2 ∨ p3)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263166369226946892351067496255 : (True ∧ ((p2 ∨ ((p1 ∨ ((p2 ∧ ((p1 ∧ (p1 → True)) → (False → p5))) ∧ (((p2 → p1) → False) → p5))) → (p2 → False))) ∨ (p4 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192177052363411721682294506454 : (((((((p1 ∧ p3) ∨ p5) → False) ∨ False) ∨ p1) ∧ p3) → ((p2 ∨ ((p3 → (p5 ∧ True)) → (False ∨ ((p4 ∨ True) ∨ p1)))) ∨ (p5 ∧ p4))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_96572820257712427046242173142 : ((False ∨ (p3 ∧ ((((((p1 ∨ p2) → ((p1 ∧ True) ∨ p3)) → p1) ∨ (True → ((((p1 ∧ p2) → p1) ∧ p2) ∧ False))) ∨ p3) → p2))) → p2) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (((((p1 ∨ p2) → ((p1 ∧ True) ∨ p3)) → p1) ∨ (True → ((((p1 ∧ p2) → p1) ∧ p2) ∧ False))) ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653955446097989405406675890237 : (((((True ∧ (False ∨ (True ∧ (((((p1 ∧ (True ∨ False)) ∨ p4) ∧ ((p4 → (p5 ∧ p2)) ∧ p4)) → p1) → p5)))) ∧ False) ∨ (p4 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50350321260557888043445131259 : ((((p5 ∧ (p2 ∨ (p4 → p2))) ∧ (p1 → (p4 ∧ (((p5 ∨ (True ∧ p1)) ∧ (p1 → p4)) → True)))) ∨ (p3 ∨ (True ∨ (p3 ∨ p5)))) ∨ False) := by
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
theorem thm_5_vars_84156321394047039396460281889 : (((False ∨ (((((True ∧ p5) ∨ p2) → p3) ∧ p3) ∧ ((p2 → p5) ∨ (p4 ∧ p1)))) ∧ ((((p1 ∨ p3) → (p4 → p3)) ∧ p2) ∧ p2)) → p3) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h3.left
      let h12 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h3.left
      let h19 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h20 := h18.left
      let h21 := h18.right
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705574916686972963438472687526 : ((((((True → p5) → (p5 ∧ (p3 ∧ True))) → p1) ∧ ((p4 ∧ (p1 → False)) ∧ ((((p3 ∨ p3) ∧ p3) ∨ ((False ∨ True) → p3)) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64069405369589978782595993479 : ((False ∨ ((((p1 → False) → ((p2 → p1) ∨ p5)) ∧ ((((True → True) ∧ p5) → False) ∧ False)) ∨ (((p1 ∨ (p3 ∨ p3)) ∧ p5) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151027803677518616397157525179 : ((((((p4 ∨ (p4 → (((True → p1) ∧ (p1 ∨ (p4 ∨ p4))) → p3))) → (False ∧ True)) ∧ p4) ∧ p5) → p4) → (p5 → ((p5 ∧ p3) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325017760346558949485892825906 : (p5 ∨ ((p2 ∧ True) → (((((p3 → (p4 → ((p1 ∧ (p2 → ((p5 ∧ True) → p1))) ∨ p5))) → p1) ∨ ((p4 ∧ True) → p5)) ∨ True) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204306975238074994291039300442 : (((False ∧ ((p2 → p4) → p5)) ∧ False) ∨ (((p1 → p4) → (False ∨ (p2 ∧ (p4 → (False ∨ (((p5 ∧ (p5 → p1)) → p2) ∧ True)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157925316952700200541028646091 : (((((p4 ∧ (False → p3)) → (p2 ∧ p1)) ∧ False) ∧ ((p1 ∨ ((False → p5) → p4)) ∨ (p5 ∨ p2))) ∨ (p3 → (True → (False → (False → p3))))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323795944596879613538990342048 : (p5 ∨ (((((p4 ∨ p5) ∧ (True ∨ p5)) ∨ p4) ∨ (((p5 ∨ ((p4 ∧ True) → p1)) ∨ p1) ∨ p1)) ∨ ((p2 → ((False ∧ p2) → False)) ∨ p1))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744508816808684358964671446896 : ((((p2 ∧ p2) → ((p5 ∨ False) ∨ ((((p4 ∨ (p5 ∨ p2)) ∧ p5) ∧ True) → ((((((True → True) → p3) ∨ p2) ∨ p1) ∧ p2) ∧ p5)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h4.left
  let h14 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h13.left
  let h16 := h13.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h17 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h20 =>
      -- One of the premise coincides with the conclusion.
      exact h20
  -- Conjunctions on the left can always be decomposed.
  let h21 := h4.left
  let h22 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h23 := h21.left
  let h24 := h21.right
  -- Disjunctions on the left can always be decomposed.
  cases h23
  case inl h25 =>
    -- One of the premise coincides with the conclusion.
    exact h24
  case inr h26 =>
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h27 =>
      -- One of the premise coincides with the conclusion.
      exact h24
    case inr h28 =>
      -- One of the premise coincides with the conclusion.
      exact h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47085334862039259275526796860 : ((((((p1 ∨ p3) → (p5 → (p2 ∧ (p1 → (p5 ∧ p1))))) → (((True ∧ (p5 ∧ p2)) ∧ p5) → p5)) → (p5 ∨ p2)) ∨ (p1 ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308524581829323148327974741622 : (p2 ∨ ((((((False ∧ p2) → p4) → (p3 ∧ ((p2 ∨ p2) ∨ (p5 ∧ p1)))) ∧ p2) ∨ (p2 ∨ ((p4 ∨ ((p1 ∧ p2) → p2)) ∨ p4))) ∨ p4)) := by
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
theorem thm_5_vars_790147286544126865056649343082 : (((p5 ∨ ((p3 → False) → (p4 ∧ (((p5 → (p5 ∧ (((((p1 → p3) ∧ p5) ∧ p5) ∨ True) ∨ ((p2 → p2) → p1)))) ∨ False) → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234922321981427354815291788462 : ((True ∧ True) ∧ ((p2 ∨ ((p5 → (p5 → p4)) → (False ∨ p2))) ∨ ((((p4 ∨ p1) → (p2 ∨ p2)) ∧ (p5 ∧ p5)) → (False → (p3 → p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615378115417291280286865935533 : ((((((p2 ∧ p3) ∧ ((((False ∨ (True ∨ (p4 → (True ∨ p1)))) ∧ p1) ∨ p3) ∨ p1)) ∨ ((p5 ∨ (p3 ∧ (p5 ∧ p2))) ∨ p4)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147551272657455765525575903112 : (((p5 → ((p5 ∧ ((p2 ∨ (p1 ∨ ((p3 ∧ (p1 ∧ False)) ∧ p2))) ∧ (p3 ∨ (p1 → False)))) ∨ True)) ∨ p1) ∨ ((True → (p5 → p1)) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247528391900230942159568442267 : ((False ∨ p4) ∨ ((((((p3 → p2) → (((p2 ∧ False) ∧ (p3 ∧ (p5 ∨ True))) ∨ (p2 → ((p3 ∨ p5) → p3)))) ∨ p1) → True) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39529770668626675811775184371 : (((False ∨ ((p5 ∨ (((True ∨ (False ∨ p5)) ∧ (p2 ∧ p1)) ∨ p2)) ∨ ((p2 → (((p3 ∧ True) → False) ∨ True)) ∧ (p5 ∨ p3)))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328620373276245701400365849513 : (True → (((p3 ∧ p5) ∧ ((p1 ∧ (p3 → (False ∧ (p3 ∨ (False ∨ False))))) ∨ p4)) ∨ ((True → ((True → p5) ∨ (False ∨ p5))) → (p5 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629083010917557788034982242473 : ((((((((True ∨ p1) → ((p5 ∨ (p3 → p1)) → (((p5 ∨ p4) ∧ True) ∨ (p5 ∧ ((p4 ∨ p3) → p2))))) ∨ p5) ∨ False) ∨ False) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230678258897926789814183389000 : (((p4 → True) ∧ True) → ((False ∨ (((p1 ∧ (p1 ∧ ((p2 ∨ p2) → (p2 → True)))) ∧ (((p3 ∨ p3) → p5) ∧ p5)) ∨ (p2 → p3))) ∨ True)) := by
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
theorem thm_5_vars_307241482317777804333643005369 : (p1 ∨ (p2 ∨ ((((p5 → (((True → ((p4 ∧ True) → (p2 → p1))) ∧ False) ∨ (p5 → p5))) → (p3 ∧ (p3 ∨ True))) ∨ (p2 ∨ True)) ∨ False))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198396934123538941104807332515 : ((p3 ∧ (p5 ∨ (False ∧ ((False → p3) ∧ False)))) ∨ (p4 ∨ ((((((p2 ∧ True) ∨ ((p5 ∨ (p1 ∨ p4)) ∨ False)) ∧ p5) → True) ∨ p1) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_688926555661902774862551518347 : (((((p3 ∧ (((((p3 → False) ∨ p2) ∨ True) ∧ (p3 → (p5 ∨ True))) → p2)) ∧ True) ∨ (((True → p1) ∧ p4) → ((p2 ∧ True) ∨ p1))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326951073253435554883876281329 : (True → (((((p2 → (p1 ∧ (False → (False → (p4 ∨ (p4 ∧ p5)))))) ∨ (((p3 ∧ (p2 → False)) ∨ p5) → False)) → p4) ∨ (p4 → True)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172988432104315751839337097048 : ((p5 ∧ ((((False ∧ ((p1 ∧ p5) ∧ (p5 → p1))) ∧ True) ∧ (p3 ∧ p3)) ∨ False)) ∨ ((True ∧ p3) ∨ ((p3 → False) ∨ ((True ∧ True) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153136602813029763094616050259 : ((p4 ∧ (p2 ∨ ((p1 → (p3 → ((((p2 → True) → ((p1 ∨ p2) → (False ∧ p2))) ∨ p3) → p3))) ∨ p3))) → ((False ∧ p3) ∨ (p2 ∨ True))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139461292984867204224975709778 : (((((p3 ∧ (((True → p1) ∨ (True ∨ p5)) ∨ p3)) → ((((p2 ∨ p5) ∧ (p4 ∧ p3)) ∨ p1) ∨ False)) ∨ True) → False) → ((p4 ∨ p1) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (((p3 ∧ (((True → p1) ∨ (True ∨ p5)) ∨ p3)) → ((((p2 ∨ p5) ∧ (p4 ∧ p3)) ∨ p1) ∨ False)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626761417844927398543469800554 : ((((p5 → ((p3 → ((True → p2) ∧ (((p2 ∨ p3) ∧ p3) → (p5 ∧ ((p1 ∨ (p1 ∧ (True ∨ True))) ∧ True))))) ∨ (p5 ∨ p2))) ∨ p1) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253722336960071614749208542381 : ((p1 ∧ p1) → (((((((((p4 ∧ p4) → p1) ∧ p1) ∨ False) ∧ (False ∨ ((p1 → (p2 ∨ False)) ∨ p3))) ∧ False) ∧ (p1 ∨ True)) ∨ p1) ∨ p2)) := by
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
theorem thm_5_vars_230640540398205899492271030534 : (((p3 → True) ∧ p1) → ((((((p5 → p1) ∨ False) → ((p3 ∨ p4) → (p2 ∨ (True ∨ (p4 ∧ p3))))) → (False ∧ True)) ∨ (p4 ∧ p5)) → p5)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : (((p5 → p1) ∨ False) → ((p3 ∨ p4) → (p2 ∨ (True ∨ (p4 ∧ p3))))) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- False on the left can always be used.
          apply False.elim h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- False on the left can always be used.
          apply False.elim h14
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h15 := h3 h6
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h1.left
    let h21 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148817489771037756054556051579 : ((((p5 → False) → ((p5 → p2) ∧ p4)) → (p5 ∧ (True ∧ ((False ∧ (False ∨ p1)) ∨ (p1 ∧ (p3 ∧ p1)))))) ∨ ((p4 ∨ p2) → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135992743277957051096153069088 : ((((True ∧ p3) ∧ (p5 ∨ (p4 → ((True ∨ False) ∧ p1)))) ∨ (((False → (p2 ∧ p3)) → (p3 ∧ (p1 ∧ p1))) ∨ p2)) ∨ (p1 → (p1 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111333450527337500688588183797 : (((p2 ∧ (p1 ∨ (p5 → (((True ∧ False) ∧ p1) ∨ (False ∧ (p2 ∧ ((p1 ∨ p5) ∧ ((p5 ∨ (False ∧ True)) → p1)))))))) ∧ p1) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258731949303343803205228308301 : ((True → True) → (((False → (False → p1)) → p5) → (((((p2 → (p5 ∧ p5)) ∨ p1) ∨ (((p1 ∧ p4) ∨ p5) ∨ True)) ∧ True) → (p1 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740643469137588938255010838882 : ((((p2 ∨ p2) ∨ (((p2 → ((((p3 ∧ True) ∧ p3) → p5) ∨ p3)) → (p2 ∨ p2)) → (p1 ∨ ((p1 ∧ (False → p2)) → (True → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172314635702636673315908351737 : (((p1 ∨ ((True ∧ True) ∨ ((p5 ∨ p1) ∧ True))) → ((p4 ∨ (p4 ∧ p3)) ∨ True)) ∨ (((((p3 ∧ p1) ∧ p1) ∧ (False ∧ p4)) ∨ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666376931747047180311633981825 : ((((((p4 → (((True → p3) ∧ (((p4 ∧ (p3 ∨ p5)) ∨ p4) ∧ p4)) → False)) → p4) ∨ (p3 ∨ (p5 ∧ p3))) ∧ (p2 → (p5 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111516921920340770917365677153 : (((p5 → ((p4 ∨ (((False ∧ True) → p4) ∨ (False ∧ (p5 ∨ False)))) → (((p4 ∨ p1) ∧ p3) ∨ ((p4 ∧ True) ∧ p2)))) ∧ p1) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125467898631681017331552463504 : (((False ∨ p1) ∧ (((((p5 → p3) → (p2 → (p3 ∨ ((p1 → (p5 ∨ (p5 ∨ p2))) ∧ p3)))) ∧ p2) ∨ (p4 → p4)) → False)) → (p3 ∧ p1)) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : ((((p5 → p3) → (p2 → (p3 ∨ ((p1 → (p5 ∨ (p5 ∨ p2))) ∧ p3)))) ∧ p2) ∨ (p4 → p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h6
    -- False on the left can always be used.
    apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157567766394249051584334565218 : (((((p1 ∧ p5) ∨ (p2 ∧ p3)) ∧ (((False → (False ∨ (p3 → True))) → p3) → p2)) → (True → False)) ∨ (p3 → (p2 ∨ (p2 ∨ (p3 ∨ p5))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344729342509210696321426990214 : (p2 → (p3 → ((((p5 ∧ (((p3 ∨ False) ∨ p2) → False)) → (p2 ∨ ((False ∧ p5) → (False ∨ p3)))) → p4) ∨ (((p4 → p1) → p3) ∧ p2)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45528520009265920201049774474 : (((p1 ∨ ((True ∨ p3) → (((((p1 → (False → p1)) ∧ (((p1 ∧ (p4 → (p2 ∨ False))) → p1) → p5)) ∨ p3) ∧ p5) ∧ p1))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64972285477113452432290221467 : ((p2 ∨ ((p1 ∨ ((p3 ∧ p1) → (p4 ∧ p3))) → (((p1 → (((p5 ∨ p1) → (p4 ∨ (p2 ∨ p5))) → False)) ∧ p3) ∨ (True ∨ p5)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199444266242920393778457944378 : (((p2 ∧ (((p2 ∨ p5) → p2) → p5)) ∨ p5) → (((p5 ∧ (p4 → True)) ∨ p5) ∨ ((p4 ∨ ((((True ∨ p5) → p3) → p1) ∨ p1)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : ((p2 ∨ p5) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351408831883760322175203933546 : (p4 → (((((p1 ∧ (p3 ∨ p3)) ∨ p3) ∨ p3) ∨ ((((p4 → (p4 ∧ p3)) → True) ∨ (p3 ∧ False)) ∧ True)) ∨ (p5 ∨ (True → (p3 → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168423975058243261101071020692 : (((True ∨ True) → (((((p3 ∧ (p2 → False)) ∧ p5) ∨ p5) ∨ (p3 ∨ p2)) ∧ (False ∧ p5))) → (p5 → ((p1 → (p2 ∨ (p1 ∧ False))) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608119917558737532630537504369 : ((((((((((((True ∧ p3) ∧ p1) ∨ p4) ∧ False) ∧ ((p3 ∨ p4) ∨ p2)) ∧ p5) ∨ ((p1 ∧ (p5 → p5)) → True)) ∧ p4) ∨ p1) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158975670629431780755620877538 : ((p3 ∨ ((p5 → (((p3 ∨ p1) ∧ (((False ∧ p5) → (p3 ∨ p3)) ∨ False)) ∧ (p2 ∨ False))) → p1)) ∨ (False ∨ ((p5 ∧ (True ∧ p5)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171680952805903226165659259822 : (((p2 ∨ (((p5 ∨ p5) → False) ∧ ((p4 ∨ False) → ((p2 ∨ p1) ∧ p2)))) ∨ p1) ∨ (False → ((p4 ∧ False) ∨ ((False ∧ True) → (True ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204560834780583674995793495300 : ((((False ∧ p1) ∧ (p2 ∨ p4)) ∨ p2) ∨ ((p3 ∧ False) → (p2 → (p4 ∨ (((p4 ∨ p3) ∨ ((p1 ∨ False) → p5)) ∨ (p4 ∧ (p2 ∨ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



