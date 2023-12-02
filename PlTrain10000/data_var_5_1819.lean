variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165236055780183380122388539609 : (((True ∧ (((p2 ∨ p5) ∨ (p2 ∧ (p1 → ((True ∧ p5) ∧ True)))) → p1)) ∨ (p2 ∧ False)) ∨ ((False ∧ (False ∧ (True ∧ p2))) → (p2 ∧ p5))) := by
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
theorem thm_5_vars_66278686974187587419387402339 : ((p5 ∨ ((p1 ∨ (p1 → p4)) → (((p4 ∧ (p5 ∧ (p3 ∧ p5))) ∨ ((p3 ∧ p1) → (((p5 → p2) → p2) ∨ False))) ∨ (p5 ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322219689588112250118460644571 : (p5 ∨ ((((True ∨ (p2 → (p4 ∨ p2))) → (False ∨ (((((p1 → p5) ∨ (p4 ∨ p4)) → ((p3 → False) ∨ p2)) ∨ p2) → p1))) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316486101794799272715444113517 : (p3 ∨ (p2 ∨ (((((True ∧ p3) ∧ False) ∧ ((False ∧ (((p1 ∨ ((((True ∨ p2) → False) ∧ p4) → p5)) ∧ p2) ∧ False)) → False)) ∧ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710531002684498745165572924656 : (((((p4 → (True → (False ∨ True))) → p2) ∧ (((((p3 → True) ∨ (p1 ∧ ((p4 → (p2 ∨ p2)) → p4))) ∧ p1) ∨ p5) → (p4 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226057140066624966147115973730 : (((p5 ∧ p3) ∨ False) ∨ (((p2 ∧ (False ∨ (True ∨ (False ∧ p2)))) ∨ True) ∨ ((p2 ∨ False) → (False → ((p4 ∧ (False ∧ (p5 ∧ p1))) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327131380739680515687730693233 : (True → ((True ∧ (p4 ∨ ((False ∧ ((p4 ∨ (True → (p2 ∧ p1))) → ((p1 ∧ (p3 ∨ (p5 ∧ (False ∧ (p2 ∨ p2))))) → p5))) ∨ True))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_128026843069444246162100720428 : ((p1 → ((((p1 → False) → p2) → p2) ∧ (p2 → (p5 ∧ ((((True → False) ∨ p3) → p4) ∨ (True ∨ ((p4 ∨ p4) → p4))))))) → (p4 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2741721617322487459095213700 : (((p1 ∧ False) → (p5 → p3)) ∧ (((((p2 ∨ p4) → False) → (p3 ∨ False)) ∨ (p2 → (p1 ∨ (p3 → p2)))) ∨ ((p2 ∨ p1) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347140679061205975451151259295 : (p3 → ((((p4 → p1) ∧ p1) ∧ ((False ∨ False) ∨ (p5 → ((p2 ∧ False) ∧ True)))) → (p5 → (p4 ∨ (p4 ∧ ((p1 ∧ p2) → (False ∧ p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302639587313619767297165614188 : (False ∨ (p2 ∨ ((p3 ∨ ((p2 ∨ (False → (True ∨ (((p5 ∨ False) ∨ p1) ∨ p1)))) ∧ False)) ∨ (((p5 → True) ∨ True) ∨ (False ∨ (True → p2)))))) := by
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
theorem thm_5_vars_345549352075805557138461875047 : (p3 → (((p4 ∨ (((p3 → p3) ∨ False) ∧ p4)) ∨ (p5 ∧ ((p4 ∨ False) → (((p5 ∨ (False → True)) → p5) ∧ (p5 ∧ (p1 ∨ True)))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54710331409629006752749718812 : ((((p3 ∨ ((p5 → p1) ∧ True)) ∨ (p2 → True)) → (p3 → (((((p4 ∨ p3) ∧ (p2 ∨ (p5 ∨ p5))) ∨ (p1 → p2)) ∨ True) ∨ p1))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142739702967918586353988307206 : ((p2 ∨ ((False ∧ ((p3 ∧ p1) ∧ p3)) ∨ (p3 ∧ ((True → ((p4 → True) ∨ ((False ∧ p1) → True))) ∧ (False ∨ p1))))) → ((True → False) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149965098075193096352372679073 : ((p4 ∨ ((False → (((((p4 → p5) ∨ p4) → False) ∨ p2) ∨ ((False ∧ ((p2 ∧ p1) → p4)) → p1))) → p1)) ∨ ((True → False) → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37344804158119112313976879254 : (((((True → (((p5 ∧ p4) → ((p1 ∨ (p4 → ((((True ∧ p5) ∨ p5) ∧ p1) → (p4 ∧ p5)))) → p1)) ∨ p4)) ∧ p5) ∨ False) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340955561016576803262107747377 : (p2 → (((p1 → (p3 ∧ p4)) ∨ (p1 ∨ ((((p2 ∧ p5) ∨ ((((p2 ∨ (p5 ∧ p4)) ∧ p4) ∨ p3) ∧ True)) ∧ (p3 → p4)) → False))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44125967917394598247405026907 : ((((((p1 ∨ False) ∧ False) → (((p5 ∧ ((True ∨ p2) ∧ (False ∧ p4))) → ((p3 ∨ p1) ∨ p5)) ∨ p3)) ∨ ((True ∨ p2) ∧ p5)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124807623883655438087323063468 : ((((False → (p2 ∧ p1)) ∧ False) ∨ (((True ∧ p1) ∧ ((p5 → (True ∨ p3)) ∧ ((((p4 → p5) → p4) ∨ p4) ∧ False))) → p5)) → (p1 → p1)) := by
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
    apply False.elim h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60487914648954755667891271281 : ((True ∧ (((((p1 ∨ True) ∨ (((p2 ∧ True) ∨ p5) → ((((True ∧ (False ∨ p3)) ∧ (False → p4)) ∨ p2) → False))) ∨ p3) → p4) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111505291314952849803099146397 : (((p4 → ((False → ((p5 ∨ (False ∧ (p2 ∧ False))) ∧ ((p4 → (p1 ∧ p2)) → p5))) → (True → ((p2 ∨ p1) → False)))) ∧ False) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48220935633506557242574062908 : ((((p5 → p1) → (p3 → (p1 ∨ (p1 → (((False ∨ p3) ∨ p3) ∨ (p2 ∨ (True ∨ (p1 → ((p2 ∧ False) ∧ p4))))))))) → (p2 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717901829397104754111240395501 : (((((p3 ∨ (p3 ∨ False)) ∧ True) ∨ (p1 ∨ ((((p3 ∧ True) ∨ p3) ∨ p4) ∨ ((p3 → ((p1 ∨ False) → ((False → p1) ∨ True))) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158084377741366980070217088750 : (((p3 ∧ ((p3 → (p5 ∨ p3)) ∧ True)) → ((p4 → (((False ∧ False) ∨ p4) → p2)) → (p5 ∧ p5))) ∨ (((False ∨ False) → p4) ∨ (p4 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190510263470356020712635071444 : ((((p5 → (((p5 ∧ False) ∨ p4) → p2)) ∨ p1) → p3) ∨ (((True → ((False ∨ p2) ∨ (p1 ∨ p1))) ∨ p2) ∨ ((p2 ∨ True) → (p3 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208203591814890348009030605755 : (((True → (p5 → p3)) → (p2 ∨ p2)) → (((((p2 → p3) → ((p5 ∧ (p3 ∨ p5)) → ((p4 ∧ p5) ∨ True))) → False) → (False ∧ p3)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 → p3) → ((p5 ∧ (p3 ∨ p5)) → ((p4 ∧ p5) ∨ True))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
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
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h3
  -- False on the left can always be used.
  apply False.elim h10
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h11 : ((p2 → p3) → ((p5 ∧ (p3 ∨ p5)) → ((p4 ∧ p5) ∨ True))) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h18 := h2 h11
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59564302520873624303968660047 : (((p3 → p4) ∨ (((p5 ∨ p2) ∨ ((p1 ∨ (p5 ∧ ((((((False ∧ False) → p2) ∧ False) → p3) ∧ (True ∧ False)) ∧ p4))) ∨ p3)) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677663877834651115099074545757 : ((((((((False ∨ ((p5 ∨ False) ∨ p5)) ∧ False) → (p4 ∨ (True → p1))) ∧ ((p3 ∧ p1) ∨ p3)) → p2) ∨ (p2 → (False → (p4 ∨ p4)))) ∨ p2) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352036920517005358533407259420 : (p4 → ((((p2 → p4) ∨ False) → (True ∨ (p5 ∧ p2))) → ((((p2 ∨ ((p2 ∨ True) ∨ ((p3 ∨ p3) → p4))) ∧ (p2 ∧ p3)) ∨ p1) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117086785430483745200414346719 : (((False → p5) → (((((((p5 ∨ p2) ∧ p2) → (True ∧ (True → (p5 ∨ True)))) ∧ ((p3 ∨ p5) ∨ False)) → p5) ∧ p2) ∨ True)) ∨ (p2 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_395098038339224210825908267019 : ((((False ∧ ((p3 ∧ True) → (((False → (p3 ∨ (False → ((((p1 → p2) → (p4 ∨ (True ∨ p1))) ∨ True) → p3)))) ∨ True) → p5))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_114462514327018792709636572690 : (((((p2 ∨ (p3 ∧ (p5 ∧ (p4 ∨ (False ∧ p3))))) ∨ (p5 ∨ ((p5 ∧ False) ∨ p5))) ∨ p3) → ((p3 ∨ p3) ∨ (p4 ∨ False))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339483296153022494693654963721 : (p1 → (False ∨ (((p2 → p2) ∧ (((((True → (p2 → False)) ∨ ((p2 ∧ (p3 → p2)) → p1)) → p5) ∧ p5) ∨ (p3 → (p4 ∨ p1)))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41129743072404083686503930065 : ((((((p5 ∧ (p3 → (p2 ∨ p5))) ∧ (p3 ∧ ((((p2 ∨ (p5 ∧ p2)) → p5) → p4) → p1))) ∨ p2) ∨ (True ∨ (p1 → p3))) ∨ p3) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112472730747857843823379779223 : (((((True → (p3 → p5)) ∧ (False ∨ ((p3 → (False ∨ (((False ∧ (True → p3)) ∧ (p1 ∨ p4)) → p3))) ∧ p1))) ∨ p4) → p4) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_471896501067986170700051877790 : (((((((p5 ∨ p4) ∨ True) ∧ (p2 ∧ p1)) ∧ (p5 ∨ (p1 ∧ p1))) ∨ (p3 → ((((p3 ∧ False) ∧ p4) ∧ p1) → (p4 ∧ (True ∧ p2))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- False on the left can always be used.
  apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_458117854343245198617093668635 : ((((((p2 → p4) ∨ p5) ∨ ((True → p2) ∧ ((p5 → (p1 ∨ (False ∧ p5))) → (p3 → p5)))) ∨ (((p1 → (p4 → p1)) → False) → p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → (p4 → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789013850541755534627706960213 : (((p5 ∨ (((((p5 ∨ (((p4 ∨ p5) ∨ (False ∨ False)) ∨ p5)) ∧ (False ∧ False)) → (p4 ∨ (p2 → p5))) ∨ (p1 ∧ False)) → (p1 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180738192071376682077467287764 : ((((p2 → (p5 ∨ False)) ∨ True) ∨ (((p4 → p5) ∨ (p1 ∧ p1)) ∨ False)) → (((p5 ∨ ((p3 ∨ p5) → p3)) → p5) ∨ ((p1 ∧ p2) → True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647473709859618206230309834344 : ((((p4 → (p5 ∨ (p3 ∧ (((True → p4) → (((p5 ∧ False) ∧ ((False → p5) ∧ (p1 ∨ p5))) ∨ p4)) ∧ (True → (True → True)))))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748437958804312876844584776629 : ((((p2 → p4) → ((((((p1 ∧ p1) ∨ p4) → (p2 → p5)) → p5) ∨ p4) → ((p5 ∧ (p1 ∧ ((p1 ∨ p3) ∨ p3))) ∧ (p5 ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38759146130105468787581002834 : ((((False ∧ (p5 ∨ (p5 → p2))) ∧ ((((p1 ∨ p1) ∨ p1) ∧ p1) ∨ (((p3 ∧ (p5 ∨ False)) ∧ ((True ∨ p3) ∨ p4)) → p1))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717285233359390077346644174187 : ((((p4 ∨ ((True → p2) ∨ p2)) ∧ ((p2 ∨ (p1 → p5)) ∧ ((p1 ∨ (False ∨ p1)) ∧ (True ∧ (p3 → (((p3 → p2) ∧ p3) ∨ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147323222945360397654841841785 : ((((((((((p2 ∨ False) → (False ∧ (p3 → p2))) ∨ p1) ∨ p2) → p2) ∨ p5) → p3) ∧ (False ∧ p1)) ∨ True) ∨ (p5 ∧ (False → (p2 ∧ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52232415681183056454656558582 : (((p2 ∧ ((((((p3 → p4) ∨ (p2 ∧ True)) ∧ (p3 → p1)) ∧ p3) ∨ p3) ∨ p4)) → ((((False ∨ p2) ∨ False) ∧ (p4 ∨ p5)) ∨ p3)) ∨ p5) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52275401513982807767171010852 : (((p1 → ((True ∨ p2) ∧ (True → (p5 ∨ ((p2 → ((p2 ∧ p5) ∨ True)) → p5))))) → (p5 ∧ ((p2 ∧ (p3 ∨ (True → True))) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110868016596439896865746954820 : (((((((p1 → (p5 → p3)) ∧ (True ∧ ((True ∨ True) → p5))) ∧ (p3 ∨ (True ∧ ((p4 ∧ p2) ∨ p4)))) → p2) → p5) ∧ p2) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304789416516570802619019656309 : (p1 ∨ ((p5 → ((p4 → (True → (((p3 ∨ ((((p5 → p2) ∨ False) → True) ∧ p5)) → p1) ∧ ((p5 ∨ True) ∧ p1)))) → p1)) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601640875840267590806297726845 : ((((p3 ∧ (p2 ∧ ((p5 ∨ (True ∧ (((p1 ∧ (p3 → True)) ∨ (p5 → p2)) ∧ (False → (p1 → ((p2 ∧ p3) ∨ False)))))) ∧ p5))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259505017359063982721011974306 : ((False → p5) → ((p2 ∧ (p3 → ((p2 ∨ ((p2 ∧ (((((True ∨ p5) → (p3 → True)) → p2) ∨ p4) → True)) → p5)) ∨ True))) ∨ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609669479985957872335720576774 : (((((p1 ∨ ((((p4 ∧ (p1 → ((True → ((p1 ∨ (True ∧ True)) → False)) ∨ p2))) ∨ ((p5 ∨ False) ∧ True)) → True) → p2)) ∨ p4) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_627188523543419145623108397268 : ((((((((((p1 → p1) ∧ p4) ∨ (p1 ∨ True)) ∧ (p4 ∧ (p1 ∧ ((False ∧ (True ∧ p2)) ∨ p2)))) → (True ∨ False)) ∨ True) ∧ True) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232406023018783091207981013702 : (((p5 → p5) → False) → (p5 → (False ∧ ((True → (((p2 → (p3 → p1)) → ((p1 → p2) ∧ (True → (p1 ∧ p2)))) ∨ p5)) ∧ (p1 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p5 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p5 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h7
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125566379466099288269179457306 : (((p2 → False) ∧ (p2 ∧ ((True → p5) ∧ (((p1 ∧ (p1 ∨ (p1 ∧ (p3 → ((True ∧ p5) ∨ p5))))) ∧ p5) → (True ∨ p1))))) → (p3 ∧ True)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149944658922075840203503444819 : ((p3 ∨ (p1 ∨ ((p4 ∨ ((p2 ∧ True) → ((((p1 → False) ∨ False) ∧ (p1 ∧ p1)) ∨ False))) ∧ (p5 → True)))) ∨ (((p3 ∨ p3) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45275334685968317121153703867 : (((p2 ∧ ((p5 ∨ (False ∧ (p2 ∧ (p5 ∧ ((p4 → (p1 ∨ p5)) → ((True → (False ∨ p3)) ∨ (p3 → (p1 ∧ p1)))))))) → True)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4156812245719551903856275004 : (p4 ∨ ((((((p4 ∨ (p5 ∨ p5)) ∧ (p1 ∨ (p3 ∨ (p5 ∧ (False → p1))))) ∨ (p1 ∧ True)) ∨ (p5 ∨ p2)) → p1) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212589599772450380432140579225 : ((p5 ∨ (p3 ∨ (False ∨ True))) ∧ ((((((True → True) ∨ ((True ∨ False) → p2)) → ((p4 ∧ (True ∧ p3)) ∧ (False ∨ p1))) ∧ p2) ∧ True) → p1)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((True → True) ∨ ((True ∨ False) → p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336398024750147180808605483880 : (p1 → ((p3 ∧ (((False ∧ ((p5 → p4) → p4)) ∧ p4) ∧ ((((p1 ∨ ((((p1 ∨ p4) → p1) ∨ p5) ∨ p5)) ∧ p4) ∧ p3) ∨ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194241020515291827303211034613 : ((p4 → (((p2 ∧ p2) ∧ False) ∨ (p4 ∧ (p5 → p4)))) → ((((p2 → (p4 ∧ p2)) ∧ p5) ∨ ((True → p1) → False)) ∨ (True ∨ (p3 ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204207790954528134392240462358 : (((((p4 ∨ p5) → p3) → p4) ∧ p2) ∨ (p5 ∨ (((p5 ∧ p2) ∨ ((((p1 → (p3 ∧ p5)) ∧ True) → p1) → p4)) ∨ ((True → True) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_629817289370648569243348595314 : (((((((p1 ∨ (p5 ∧ (True → ((p3 ∨ p2) ∧ p1)))) ∧ True) ∧ (p5 → ((p1 ∨ p3) → (p3 → (False → (p3 ∨ p2)))))) ∨ p4) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206241871520792361254878211987 : ((False ∨ (((p2 ∨ True) ∧ p4) ∧ False)) ∨ (((p2 ∧ (((p3 ∧ False) ∨ (False ∧ (p2 ∧ (p1 ∨ ((p3 → p4) → p5))))) → p5)) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54489479527283946895892907845 : (((((p1 → True) ∨ (p2 → p1)) → (False ∨ p2)) ∨ ((((p4 → (p5 → ((p3 ∨ False) ∨ (p2 → True)))) ∧ (p4 ∨ p5)) → p3) → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748826573829066322466700267654 : ((((p4 → False) → ((((((True ∧ p4) → (True → p2)) → p2) → ((True → (p4 ∨ (p5 ∨ p1))) → True)) → False) ∨ ((p1 → p4) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304148450729459189939370003177 : (p1 ∨ ((((p4 ∨ (p2 ∨ ((True → p5) ∨ (((False ∧ p4) ∨ p1) ∨ p5)))) → ((False → (p5 ∧ (p3 ∧ p5))) → (p3 ∧ p3))) ∧ p1) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p4 ∨ (p2 ∨ ((True → p5) ∨ (((False ∧ p4) ∨ p1) ∨ p5)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (False → (p5 ∧ (p3 ∧ p5))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347223294574560437569152328460 : (p3 → (((p3 ∧ (p1 ∨ (p4 ∧ ((p4 ∨ p1) → p3)))) ∨ (p2 → p3)) → ((((p5 ∨ (True → True)) ∧ False) ∧ (p2 ∧ (False ∨ p1))) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_298709085849265638301242735996 : (False ∨ (((((True → (p3 → p2)) ∧ (((p5 → p4) ∨ ((((True ∨ True) ∨ p4) ∨ (p1 ∨ p4)) ∨ p3)) ∧ p3)) → (p4 ∨ True)) ∨ p4) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731585316649100133307722310235 : ((((p1 → (False ∧ p3)) → (p2 ∨ (p1 ∨ ((p4 ∨ True) ∧ (((((p4 → True) ∧ ((p5 ∨ p4) → (p5 → p4))) ∨ False) ∨ True) ∨ p2))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158518108669558989696749391532 : (((p3 ∨ True) → (p1 ∨ ((p2 → (((((False ∧ p3) ∨ True) ∧ p2) ∧ p5) ∨ p3)) ∨ (False ∨ p5)))) ∨ (((False → p5) ∨ p5) → (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60107470107309630127459584289 : (((p3 ∨ p2) → (p1 ∧ ((((p4 ∨ (((p4 ∧ True) ∧ (p5 ∧ p5)) ∧ (p1 ∨ True))) ∧ False) ∨ True) ∨ (False ∨ ((p4 ∨ p5) → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134068586676697340994863967241 : (((((((((p4 ∧ True) ∨ True) ∧ p3) ∧ ((p3 → (((p2 ∨ p5) ∨ p1) ∧ p2)) → False)) ∧ p2) → p3) → p3) ∨ False) ∨ ((False → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161415083749256407854250408963 : ((p2 ∧ (((p3 → ((p1 ∨ True) → p5)) → ((False ∨ p5) ∨ ((p3 ∨ (p5 ∨ p5)) ∨ p2))) ∧ p3)) → (((p5 ∧ (p3 → False)) ∧ p1) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53138046465678661946023383047 : (((((True ∨ p3) → (((p3 ∨ p5) → p2) ∨ (p2 → p3))) ∧ True) ∨ ((True ∨ False) ∧ ((((p4 ∨ (p4 ∧ p4)) ∧ p4) ∧ p1) ∨ True))) ∨ p4) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783498412577409222208812815644 : (((p3 ∨ ((True ∨ ((False ∨ (p4 ∧ (p1 ∧ p1))) ∨ ((p3 ∨ True) ∨ p2))) ∧ (((((p4 ∧ p3) ∨ (p3 ∧ p1)) → True) ∨ p4) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191095852437677342321742471698 : ((((p1 ∧ p1) → p4) ∧ (p1 ∧ ((p1 ∧ False) ∨ p1))) ∨ ((p1 → ((p2 ∨ True) ∨ p3)) ∨ ((p4 ∧ p1) → (p4 ∧ ((p2 → True) ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32315674426562923538177554015 : ((p1 ∨ (p3 ∨ ((p3 ∧ ((((p1 ∧ p4) → p2) ∧ (True → ((True → p1) ∨ p5))) → ((True ∧ p5) → False))) ∨ ((True ∨ p1) → True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808442558596487005139380900377 : (((p4 → (p2 ∨ (p1 → ((((p1 → p4) → False) → p4) → (((((p2 → False) → p5) → (((p5 ∧ p1) → p5) → p5)) ∨ p3) ∨ p4))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133882888479482491102197187856 : (((p5 ∧ ((True → ((False ∨ p3) ∨ False)) ∧ ((p3 ∧ (p4 ∨ True)) ∨ (p4 → ((p2 ∨ (True → False)) ∧ p4))))) ∧ p4) ∨ (p1 ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768304931360447875983187319679 : (((p5 ∧ (((p5 ∨ (p1 → (True ∨ p4))) → (True → (False ∧ ((p5 ∨ ((False → p4) ∨ (p3 → p1))) → p2)))) ∨ ((p1 ∨ p2) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113980858316493452146194291612 : (((p1 ∨ (p5 ∧ (((p3 ∧ False) ∧ ((((p1 ∨ False) → ((p3 ∧ True) → p5)) → p4) → p3)) ∧ p2))) ∧ ((p2 ∨ False) ∧ p3)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61816551881328124972022564878 : ((p2 ∧ ((((True ∨ (p1 ∨ (p5 → p2))) ∨ p3) → (p2 ∨ ((p5 ∧ p2) → (((p1 → (p1 → p1)) ∨ p3) ∨ (False → p5))))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178986646127094540185744204683 : (((p3 → False) ∨ (((p5 ∧ (p1 → p5)) → False) → (p2 → (True ∧ p5)))) ∨ (p3 ∨ ((p3 ∧ ((True → p2) ∧ False)) → (p5 ∨ (p4 → p1))))) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659811124545951879061725701481 : (((((p2 ∨ ((((p3 → p1) ∧ p4) → (((((p4 → p1) → p1) → p5) ∨ True) ∧ False)) ∨ ((True ∧ p1) ∨ p1))) ∧ p2) → (p5 → p5)) ∨ p2) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49062273922898082242433368924 : ((((((p4 ∨ (p2 → p1)) ∨ (((p1 ∨ ((p3 ∨ p4) → (p4 ∨ p4))) ∧ False) → True)) → p5) ∨ (p3 → p3)) ∨ (p4 ∧ (p2 → p5))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260646346349135751523710128756 : ((p3 → p3) → (((p2 ∨ ((p5 ∧ ((((((p4 ∧ p3) ∨ (p1 ∨ p2)) ∧ False) ∨ False) ∨ (False ∧ p2)) ∨ p4)) ∨ (p5 → False))) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_943884273397265591281737825384 : ((((p5 ∨ (False → (p5 → p4))) ∧ (True ∧ ((p4 ∧ ((((p1 ∧ p3) ∧ p1) ∨ p4) → (p3 ∧ (p1 → True)))) ∧ ((True ∧ p4) ∨ p1)))) → p3) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h14 : (((p1 ∧ p3) ∧ p1) ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h15 := h10 h14
      -- We need to get the left conjuct of h15 based on <expert-advice>.
      let h16 := h15.left
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h18 : (((p1 ∧ p3) ∧ p1) ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h19 := h10 h18
      -- We need to get the left conjuct of h19 based on <expert-advice>.
      let h20 := h19.left
      -- One of the premise coincides with the conclusion.
      exact h20
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h3.left
    let h23 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h24.left
    let h27 := h24.right
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
      have h31 : (((p1 ∧ p3) ∧ p1) ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h30
      -- We have shown the premise of h27, we can now drive its conclusion.
      let h32 := h27 h31
      -- We need to get the left conjuct of h32 based on <expert-advice>.
      let h33 := h32.left
      -- One of the premise coincides with the conclusion.
      exact h33
    case inr h34 =>
      -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
      have h35 : (((p1 ∧ p3) ∧ p1) ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h26
      -- We have shown the premise of h27, we can now drive its conclusion.
      let h36 := h27 h35
      -- We need to get the left conjuct of h36 based on <expert-advice>.
      let h37 := h36.left
      -- One of the premise coincides with the conclusion.
      exact h37
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53466544618496593246679121560 : ((((True ∨ p4) → ((p3 ∨ False) → (p4 → (p2 ∧ (p1 → p5))))) → ((p1 → ((True ∨ p4) ∧ (False ∧ (p2 → (False → p5))))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726518538027973624424468726616 : (((((p4 → False) ∨ p2) ∨ (((p5 ∨ p4) → p5) → (p2 ∨ (((((((p1 ∧ p1) ∧ (p5 → p3)) → False) → p1) ∨ p5) ∨ False) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40048891350846612756351243115 : ((((((((p3 ∧ p1) ∨ p3) → ((((False ∨ (p4 ∧ p1)) → (True ∨ (p2 ∨ p1))) → False) ∧ (p3 ∨ p1))) ∧ True) ∨ p3) ∧ p4) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53344137191516396681324971235 : ((((p1 ∧ ((p2 ∨ p1) → ((p4 → (p1 ∧ p5)) ∨ p1))) ∧ True) → ((p5 ∧ ((p1 → (p2 ∧ (p5 ∧ p1))) → p2)) ∨ (p1 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116358015493915487369002084039 : ((((p2 → p1) ∨ p4) → ((p5 ∨ ((((((p3 ∨ p1) ∧ p4) ∧ (p5 ∧ False)) ∨ p4) → (p3 ∨ (p2 ∧ True))) → p3)) → p5)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747525062944066183184012066294 : ((((True → p2) → (((((True ∨ ((p1 ∧ p4) → p4)) → ((p4 ∧ p5) ∧ p4)) → (((False ∨ False) ∧ p4) → p1)) → p1) ∨ (p2 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_460288800300456562691236356656 : ((((p4 ∧ ((p2 ∨ ((True ∧ (p5 → (p3 → False))) ∧ ((p4 ∨ p5) ∧ (p5 ∨ p5)))) ∨ p3)) → ((p1 → False) → (p2 ∨ (p5 ∨ True)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h9.left
      let h13 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h16
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h19
  case inr h20 =>
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
theorem thm_5_vars_175121611710640419439316372125 : ((p4 ∧ (False ∨ (p3 → ((p2 ∨ (p4 ∨ (((p3 → p1) ∧ False) ∨ p3))) → p4)))) → ((((False ∨ (True → False)) ∧ p2) ∨ p3) ∨ (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125553467282652731622786040208 : (((p1 → True) ∧ ((True → (False ∧ (p3 ∨ True))) ∧ (((p4 → (((True ∧ p3) → False) → ((p4 ∨ p3) ∧ False))) ∨ p1) ∨ p5))) → (p1 → p2)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h10 := h5 h9
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h14 := h5 h13
      -- We need to get the left conjuct of h14 based on <expert-advice>.
      let h15 := h14.left
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h18 := h5 h17
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353830777755326596569580895080 : (p4 → (p1 → (((p3 ∨ (p3 ∨ (p4 → ((True ∨ True) → (p3 ∨ (((((True ∨ p2) ∧ p1) ∧ p5) ∧ True) ∨ p1)))))) ∨ (p4 → p2)) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43473268330875972624790631226 : ((((True ∧ (((p1 → False) ∧ (((p1 ∧ p4) → p3) ∧ True)) → (p3 ∧ (p4 → (((p5 ∧ (False → True)) ∧ p5) ∨ p2))))) ∨ p1) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41073179056787753670354610334 : ((((True → ((False ∨ p1) → ((False → (False ∨ False)) ∧ (((p4 ∧ (p1 → True)) → (p1 ∨ p4)) → (False ∧ p1))))) → (True → False)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102665933199965885590152183934 : ((((True → (p1 ∨ ((((((((p2 ∨ p1) → p4) ∧ p4) → (False → (p2 ∧ False))) ∨ p1) → p3) ∧ p2) ∨ False))) ∧ p2) ∨ True) ∧ (False → p5)) := by
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



