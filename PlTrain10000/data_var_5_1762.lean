variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137642801284477312690389961218 : ((False ∨ ((p2 ∧ ((p4 ∧ (p4 ∨ p1)) ∧ ((p5 ∧ p4) ∨ p3))) → (p4 ∧ (p3 → ((False ∧ p3) ∨ (p4 ∨ False)))))) ∨ ((p5 → p4) ∨ p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  -- Implications on the right can always be decomposed.
  intro h18
  -- Conjunctions on the left can always be decomposed.
  let h19 := h1.left
  let h20 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h20.left
  let h22 := h20.right
  -- Conjunctions on the left can always be decomposed.
  let h23 := h21.left
  let h24 := h21.right
  -- Disjunctions on the left can always be decomposed.
  cases h24
  case inl h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h28
    case inr h29 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h25
  case inr h30 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h33
    case inr h34 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168136652982706147153964394460 : (((p1 ∧ ((True ∧ p2) → p4)) → ((p5 ∧ (p4 ∧ (p3 → ((p4 ∧ p5) ∨ p1)))) ∧ True)) → ((((False → True) → p4) → p4) ∧ (False → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209526550185065977761105185444 : ((p4 → ((False → False) ∨ (p3 → p1))) → ((((p1 ∨ True) → p1) ∨ p3) → (((p2 ∨ p2) → (p1 ∨ (((p3 ∧ p1) ∧ p1) → p2))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h6 : (p1 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h7 := h3 h6
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : (p1 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h9
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348787270172550437760281208442 : (p3 → (p1 ∨ ((((p4 ∧ p5) ∨ (((((p1 → (False → True)) ∨ p2) → ((p3 ∨ (True ∨ p5)) ∧ (False ∨ False))) → p4) ∨ True)) ∨ True) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597921798272883855011761349452 : ((((((p3 ∨ True) → p3) ∧ (p2 ∧ (((((p1 ∨ False) → (((p5 ∨ True) ∨ (p5 ∨ False)) → p5)) ∧ p4) ∧ (p4 ∨ p5)) → False))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114254493042112071974127509857 : (((p1 → ((((True ∧ p3) ∨ p4) ∧ p4) ∧ ((((True ∨ p5) → ((p5 ∧ False) ∨ p4)) → p2) ∧ p2))) → (p4 ∧ (p2 ∨ False))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803426331673468898916677252642 : (((p3 → ((p2 → (p5 ∧ (p2 ∨ (False ∧ ((p3 → ((p5 ∧ ((True ∨ p5) ∨ p4)) → (p4 → (True → (p1 ∧ True))))) → False))))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37091619960861474530359161093 : (((((p3 ∧ (((((p4 ∧ p4) ∧ p2) ∨ ((True → (p2 → p4)) ∨ p1)) ∧ p5) ∨ (p2 → (True → (p3 ∧ p2))))) ∨ p2) ∧ False) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322531632288683645452369208121 : (p5 ∨ ((p4 ∧ (((True → ((p1 ∨ ((True ∨ (p3 ∨ True)) ∨ (((p2 → (False → True)) → p1) ∨ (True ∧ p3)))) → p4)) → p3) ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790681647646440127308514866362 : (((p5 ∨ (p5 ∨ (((((p2 ∨ True) ∧ (p4 → (False ∧ p4))) ∧ p2) ∨ (p5 ∧ (((True ∧ (False ∧ p1)) → p2) → p3))) ∨ (p2 ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233779186979699513882732760555 : ((p3 ∨ (p4 ∨ p2)) → (((True ∧ (True ∧ ((p4 ∨ p3) ∧ ((p3 ∧ p5) ∧ (p2 → (p1 ∧ p1)))))) ∨ (p1 → True)) → (p1 → (p1 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h19 =>
          -- One of the premise coincides with the conclusion.
          exact h3
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h10.left
      let h22 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h25 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h28 =>
          -- One of the premise coincides with the conclusion.
          exact h3
  case inr h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h30 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h32 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h33 =>
        -- One of the premise coincides with the conclusion.
        exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198596460901289664455791955520 : ((p2 ∨ ((p1 ∨ (True → (p5 ∧ p1))) ∨ p4)) ∨ ((((((p4 → (p3 ∧ (p5 ∧ p5))) ∨ p5) → False) ∨ (True → (p2 ∨ True))) → p1) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 → (p3 ∧ (p5 ∧ p5))) ∨ p5) → False) ∨ (True → (p2 ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56735986157221811795965980244 : ((((p4 ∨ p5) ∨ False) ∧ ((True ∨ (p3 ∧ ((p2 ∨ (False ∨ ((p5 ∧ (p5 → p2)) ∨ True))) ∧ (p1 ∨ ((p3 → True) → p5))))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950265796916535664634090939442 : (((((p1 → True) → False) ∧ ((False ∨ p2) → (p4 ∨ (((p4 → ((p5 ∧ p2) ∧ p5)) ∨ (((True ∨ False) ∧ (False ∨ True)) ∧ False)) → p3)))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p1 → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197013627229268226930627813080 : (((((p3 ∨ p4) ∧ p3) ∨ (p3 ∨ p3)) ∨ True) ∨ (p1 ∨ (True → ((((p1 ∧ (True ∧ True)) → (True ∧ (p4 ∧ (p5 → p4)))) ∨ p5) ∨ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54577343615625222901164925200 : (((p1 ∨ (True ∧ (p4 ∨ (False ∨ (True → p5))))) ∨ ((p1 → p4) ∨ (((False → (p2 ∨ p1)) ∧ p3) ∨ ((p5 ∧ False) → (p2 ∧ p3))))) ∨ False) := by
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
theorem thm_5_vars_776305442859960906816146109194 : (((p1 ∨ ((True ∧ ((p1 ∨ (p1 ∨ ((False ∧ (p3 → p4)) ∧ False))) ∧ ((True ∧ True) → (p4 ∨ (p1 ∧ ((p3 ∧ p4) ∨ True)))))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4419097742579797697437060801 : (p1 → ((p1 → (p5 ∨ p5)) ∨ ((((p3 ∨ p5) ∨ (p1 → (False ∨ False))) ∧ ((p2 ∨ p2) ∨ (p3 ∨ p3))) ∨ ((p1 ∧ p1) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751468153638593748721920858029 : (((True ∧ ((p4 → p4) → ((p5 ∨ (p4 → True)) ∧ (True ∧ (p4 ∨ ((((p4 ∧ p1) ∨ (True ∧ (p3 ∧ (p1 ∧ p4)))) ∧ p5) ∨ True)))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52185326214956170550958943292 : (((((p5 → False) ∨ (p2 → True)) ∨ ((p1 ∨ False) ∧ (p5 ∧ ((p4 ∨ False) ∧ p1)))) → (((p1 → (False → (True → p1))) ∨ p1) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316653227425748840465825474714 : (p3 ∨ (p4 ∨ (p1 ∨ ((True ∧ (True → p4)) → ((((((p2 ∧ p5) → p2) ∧ p5) ∨ (False ∨ True)) ∨ ((p3 → (p5 ∧ True)) → p4)) ∨ p1))))) := by
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
theorem thm_5_vars_343628225557922645905318713420 : (p2 → (True ∧ (((((p3 ∨ (((p2 → p5) ∧ (False ∨ (p3 ∨ p4))) ∧ p3)) ∨ ((p1 ∧ p5) ∨ p5)) → (p2 → p4)) ∨ True) ∧ (p5 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158935077781368653959686148842 : ((p2 ∨ ((((((p2 ∨ p4) ∨ ((p1 ∨ False) ∨ ((True → p4) → True))) ∧ p4) ∧ True) ∨ p3) → p2)) ∨ ((False → (False → (True → p2))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173714722996401255168098358790 : (((((p4 → ((p3 ∨ (p2 ∨ p1)) ∧ (p3 ∨ False))) ∧ p5) ∨ (p3 ∨ False)) ∨ True) → (False ∨ ((p3 → ((False ∨ p2) ∨ p3)) ∨ (p3 ∧ p1)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43996654209480675141844009542 : (((((((p2 → True) → ((p1 ∧ p2) ∨ p4)) ∧ (p4 → (True → (((p1 → p2) ∧ (p3 ∧ True)) → p1)))) → False) → (False → False)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689303682570948220934674271756 : ((((((p1 ∧ True) ∧ (((p5 → p1) → p4) ∧ ((True → False) ∧ p2))) ∧ (False ∧ p3)) ∨ ((p2 ∧ (p4 ∨ (p1 ∨ (p1 → True)))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206254896989357482186612541212 : ((False ∨ (((True ∧ p2) ∨ p5) → p3)) ∨ (p3 → (((p2 ∨ ((p4 ∧ p1) → p3)) → (p1 ∧ (p1 ∨ p2))) ∨ (p1 ∨ (p3 ∨ (p5 ∧ p5)))))) := by
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
theorem thm_5_vars_735119933899765790047263967564 : ((((p3 ∨ p2) ∧ (((False ∨ p1) ∨ (((p5 ∨ p4) ∨ ((True ∧ (p3 → p1)) → (False ∨ p4))) ∨ (((p4 → False) → p2) ∨ p2))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131920607422675098938370234335 : (((p1 ∨ p4) ∨ ((((p3 ∨ (p1 ∧ p4)) ∨ (p4 ∨ False)) ∧ p3) → ((False ∧ p5) ∨ (((p5 ∨ True) → True) ∨ p1)))) ∧ (p1 → (p1 ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  -- Implications on the right can always be decomposed.
  intro h14
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172008207911187227090271836954 : ((((True ∧ ((p5 ∨ p5) ∨ ((p4 ∧ False) ∨ p5))) ∨ (False ∨ p2)) ∨ (p5 ∧ p2)) ∨ (True ∨ (p3 → ((p2 ∨ ((p5 ∧ p5) ∧ p2)) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45713941371343439963119744184 : (((True → ((p3 ∨ ((p1 ∨ True) ∧ (((p1 → p4) ∨ p3) → ((p3 ∨ p4) ∧ (False → p2))))) ∧ ((p3 ∧ p4) ∧ (p2 → True)))) → p3) ∨ False) := by
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676293763058020400968603908875 : (((((p4 ∨ (p1 → p1)) → ((((p2 → p3) ∧ (p4 → (((p1 → p2) → p4) → True))) ∧ p3) ∨ p1)) ∧ (False ∨ ((False → p4) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152399168975160520509593573172 : ((((p4 → p4) ∧ (False → True)) → ((True ∨ (True → True)) ∧ (p4 ∧ ((False ∨ (True ∧ (p5 → p5))) ∧ False)))) → ((False → (p3 → p2)) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p4 → p4) ∧ (False → True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h3
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114373534804713105303750172973 : ((((p3 → (((((p2 → ((p5 ∧ p4) ∧ (p1 ∧ p1))) ∧ False) ∧ True) ∧ p5) ∧ p1)) ∨ p3) ∨ ((p5 → (False ∨ False)) ∨ p2)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113333166819272517758132057376 : ((((p5 ∨ p1) ∨ ((p4 → (((((p4 ∨ False) ∨ (False ∧ p4)) ∨ ((p2 ∧ p2) ∨ p4)) ∧ p5) ∨ False)) ∧ p3)) ∧ (p2 → p4)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197718833096311243084638516711 : ((((True → p3) ∧ p1) ∧ (p2 ∧ (p3 → p1))) ∨ (False ∨ (p2 → ((p5 ∨ p2) → (p3 ∨ (((True → p3) ∨ False) ∨ ((p1 ∨ p4) → p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259613181642304928888669504762 : ((p1 → False) → ((((p4 ∨ ((p1 ∧ (p4 ∨ ((p2 → False) ∧ p3))) ∨ (((p5 ∧ p5) ∧ p1) ∨ p5))) → (p1 → (p2 ∧ False))) ∨ p1) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h12 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h13 := h1 h12
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h17 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h18 := h1 h17
        -- False on the left can always be used.
        apply False.elim h18
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Conjunctions on the left can always be decomposed.
        let h23 := h21.left
        let h24 := h21.right
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h25 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h26 := h1 h25
        -- False on the left can always be used.
        apply False.elim h26
      case inr h27 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h28 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h29 := h1 h28
        -- False on the left can always be used.
        apply False.elim h29
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h30 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h31 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h32 := h1 h31
    -- False on the left can always be used.
    apply False.elim h32
  case inr h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h34.left
      let h36 := h34.right
      -- Disjunctions on the left can always be decomposed.
      cases h36
      case inl h37 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h38 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h35
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h39 := h1 h38
        -- False on the left can always be used.
        apply False.elim h39
      case inr h40 =>
        -- Conjunctions on the left can always be decomposed.
        let h41 := h40.left
        let h42 := h40.right
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h43 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h35
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h44 := h1 h43
        -- False on the left can always be used.
        apply False.elim h44
    case inr h45 =>
      -- Disjunctions on the left can always be decomposed.
      cases h45
      case inl h46 =>
        -- Conjunctions on the left can always be decomposed.
        let h47 := h46.left
        let h48 := h46.right
        -- Conjunctions on the left can always be decomposed.
        let h49 := h47.left
        let h50 := h47.right
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h51 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h48
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h52 := h1 h51
        -- False on the left can always be used.
        apply False.elim h52
      case inr h53 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h54 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h55 := h1 h54
        -- False on the left can always be used.
        apply False.elim h55



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593705342552753021516285349262 : ((((((p2 → ((p3 ∨ ((p1 ∨ p5) ∨ (p3 → p1))) ∧ p2)) ∨ (p3 → ((p4 ∨ p1) → True))) ∧ (True → (False ∧ (p5 ∨ True)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330367853302952001329359708372 : (True → (p2 ∨ ((((p3 ∧ p5) ∨ ((True ∧ (p5 → (((True ∨ p1) ∧ ((p3 → (p2 ∨ False)) ∧ p4)) ∧ p4))) ∨ p5)) ∧ p4) ∨ (p4 ∨ True)))) := by
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
theorem thm_5_vars_57350816082300139879804867641 : (((p3 ∧ (False ∧ p3)) ∨ (False ∧ ((p4 ∨ p3) → (((p3 ∧ p3) ∧ (p1 → (((p5 ∨ (p5 ∧ p3)) ∨ p2) ∨ (p4 ∨ False)))) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262294875915249658455137226286 : (True ∧ ((((p5 → (((p3 ∧ (p1 → ((p2 ∧ True) → p5))) ∨ True) → p1)) → p1) ∨ ((p5 ∨ ((True ∨ p4) → (p5 ∧ p5))) ∨ True)) ∨ p5)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40130951345384750803956929999 : ((((((p5 ∧ ((True ∨ p3) ∨ (True → (p1 → False)))) ∨ (((p1 → (False → p5)) ∨ True) → p1)) → ((p4 ∨ p4) ∧ p3)) ∧ False) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342396168210356600984705870548 : (p2 → (((p4 → (p2 ∧ True)) → ((((True ∧ False) ∧ p2) → True) → (p1 ∨ (p1 ∨ False)))) ∨ (p4 → (p3 → ((False → p4) ∧ (p5 ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43655116530143573815661239757 : (((((p1 ∨ (p2 ∨ ((False → (p1 ∨ (False ∨ p1))) ∨ (p1 → (p5 ∨ (p4 ∨ (p3 ∧ p3))))))) ∨ (False ∧ (p4 → p4))) → True) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312313468939986157560884970935 : (p2 ∨ (p2 → ((((((p4 ∧ p2) ∨ p1) ∨ p5) ∨ (True ∨ p3)) ∧ p1) → ((((p5 → True) → (p5 ∧ p1)) → (p4 → (p2 → p5))) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h13 : (p5 → True) := by
          -- Implications on the right can always be decomposed.
          intro h14
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h15 := h3 h13
        -- We need to get the left conjuct of h15 based on <expert-advice>.
        let h16 := h15.left
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h18 : (p5 → True) := by
          -- Implications on the right can always be decomposed.
          intro h19
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h20 := h3 h18
        -- We need to get the left conjuct of h20 based on <expert-advice>.
        let h21 := h20.left
        -- One of the premise coincides with the conclusion.
        exact h21
    case inr h22 =>
      -- One of the premise coincides with the conclusion.
      exact h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h25 : (p5 → True) := by
        -- Implications on the right can always be decomposed.
        intro h26
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h27 := h3 h25
      -- We need to get the left conjuct of h27 based on <expert-advice>.
      let h28 := h27.left
      -- One of the premise coincides with the conclusion.
      exact h28
    case inr h29 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h30 : (p5 → True) := by
        -- Implications on the right can always be decomposed.
        intro h31
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h32 := h3 h30
      -- We need to get the left conjuct of h32 based on <expert-advice>.
      let h33 := h32.left
      -- One of the premise coincides with the conclusion.
      exact h33
  -- Conjunctions on the left can always be decomposed.
  let h34 := h2.left
  let h35 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h34
  case inl h36 =>
    -- Disjunctions on the left can always be decomposed.
    cases h36
    case inl h37 =>
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h38 =>
        -- Conjunctions on the left can always be decomposed.
        let h39 := h38.left
        let h40 := h38.right
        -- One of the premise coincides with the conclusion.
        exact h35
      case inr h41 =>
        -- One of the premise coincides with the conclusion.
        exact h35
    case inr h42 =>
      -- One of the premise coincides with the conclusion.
      exact h35
  case inr h43 =>
    -- Disjunctions on the left can always be decomposed.
    cases h43
    case inl h44 =>
      -- One of the premise coincides with the conclusion.
      exact h35
    case inr h45 =>
      -- One of the premise coincides with the conclusion.
      exact h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127683328404500890517858225638 : ((p5 ∨ ((p5 ∨ False) ∧ ((((p3 → False) → False) → p4) ∧ ((((p3 ∧ p5) ∨ False) ∧ (p3 ∧ p1)) → (p3 → (True → False)))))) → (p4 → p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149220340475105915724638785608 : (((p2 ∧ p2) ∨ (False ∨ (p4 → ((False ∧ True) ∨ (False ∧ ((p5 → (((p3 ∧ p4) ∨ p5) ∨ p1)) ∨ p1)))))) ∨ ((p4 ∨ p2) → (True ∨ p3))) := by
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
theorem thm_5_vars_112489107542452801818622687555 : ((((True ∨ ((((p1 ∧ ((True ∨ p5) ∧ (p5 → p5))) → ((p2 → (p3 ∨ p1)) ∧ p1)) ∨ p5) ∧ (p5 ∨ p5))) ∨ p3) → p3) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186715131940055063360714922202 : ((((True ∧ True) ∨ ((p3 ∧ False) ∧ False)) ∨ (p1 ∧ (p1 ∨ False))) → (((p4 ∨ ((p3 ∨ (False ∨ (False → True))) ∨ p4)) → (False ∨ p3)) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56652251269835493919419878182 : ((((p3 ∨ True) ∧ p3) ∧ ((((p3 → (p4 → False)) → (False ∧ p3)) ∨ ((p4 ∨ (False → p2)) ∨ p3)) ∨ ((p2 ∨ p3) ∧ (p5 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336275709399964680851789215598 : (p1 → ((((((True ∨ (True ∨ p5)) ∧ (p5 ∧ (False ∧ False))) ∨ False) → p2) → ((p5 → (p5 → p4)) ∨ ((True ∨ p3) → (p2 ∨ False)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353582133600683244100963805301 : (p4 → (p3 ∨ (p1 → ((True → (p5 ∨ (p2 ∨ ((((False ∧ p1) → p2) → (p5 ∧ p1)) ∧ ((False ∨ ((p3 ∧ False) ∧ p4)) → False))))) ∨ True)))) := by
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
theorem thm_5_vars_125111280084220451420469031245 : (((p4 → (p4 → p3)) ∧ ((((p4 → (p5 ∨ ((p1 ∨ ((p4 → p5) ∨ (p4 → True))) ∧ p2))) ∧ False) ∨ True) → (True ∨ p2))) → (p4 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118826427170104629030225386567 : ((True → (((p3 → p3) → ((((((False ∧ (p1 → p5)) ∧ p3) ∨ (p5 ∨ p2)) ∨ (p5 → (p1 ∨ True))) ∧ p5) → p5)) → p5)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631067432820522276101892897500 : ((((((((p2 ∨ (p2 ∧ p2)) ∨ (False ∧ (p4 ∧ ((p3 ∧ p5) ∨ p1)))) → ((True → (p1 ∧ p3)) ∨ (p2 ∧ p1))) ∨ p5) → p3) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152645928201635528614568553738 : (((True → False) ∧ ((p5 ∧ (False ∧ (((True ∨ (p2 ∨ ((p5 ∨ True) ∨ (p1 ∧ True)))) ∨ p2) ∧ p3))) → p1)) → ((p4 → p3) ∨ (p5 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59160901188796901479276376307 : (((False ∨ p2) ∨ (((False ∧ (((True → ((True ∨ ((p3 ∨ p2) → p5)) ∧ True)) ∨ p2) → False)) ∨ p4) ∨ (False → (p5 → (p2 ∧ True))))) ∨ p4) := by
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
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116067331102903494280830076637 : ((((p2 ∨ p1) ∧ p5) ∧ (((((p2 → (True → (True ∧ p3))) ∨ ((True → p3) ∨ True)) → (p1 → p1)) → p3) → (p1 ∨ p2))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136452839734766452339746098164 : (((p2 ∨ ((p1 ∧ False) ∧ p4)) → (p1 → (p1 ∧ ((p4 ∧ False) ∨ (((p4 ∧ p4) ∨ False) ∨ ((p2 → p1) → p1)))))) ∨ ((p1 → p4) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h8
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325613866417636622863426035735 : (p5 ∨ (False ∨ ((((True ∨ p1) ∧ p4) ∨ (((((((p5 ∧ p1) → (((True ∨ p2) ∧ p5) ∧ p2)) ∧ p5) ∨ p5) ∨ p4) ∨ True) ∨ False)) ∨ p3))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782388851349779875735383528616 : (((p3 ∨ (((((((p2 ∧ (((p5 ∨ p3) → p4) → p2)) ∧ (p1 ∧ p1)) → (p4 → (p5 ∨ (p4 → p3)))) ∨ False) → False) → False) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356828612658060238072640488218 : (p5 → ((True → (False ∨ (p3 ∨ p5))) ∧ ((((p4 ∧ p1) → p2) ∨ (((p5 ∧ ((((p3 ∨ p5) → True) ∧ False) ∨ p3)) ∨ p2) ∧ False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39074755949824179529782355616 : ((((p1 ∨ False) ∨ (False ∧ ((True ∨ (False → False)) ∧ (True → ((p2 ∨ (p4 ∧ ((p3 ∨ ((False ∧ p5) ∨ p2)) ∧ p2))) → p4))))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117877798674654943344961297297 : ((p5 ∧ (((p1 ∧ (((p5 ∨ ((((False → p5) ∧ (p4 → p3)) → True) → True)) ∨ p1) ∧ (p3 ∧ p4))) → (p1 ∨ p2)) → p1)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173329364013338727522937925104 : ((p2 → (((False → p2) → (False → (p4 ∨ p1))) → (False ∨ (False ∧ (False ∨ p1))))) ∨ ((p2 → p3) ∨ (p4 → (p1 → ((False ∨ p4) ∨ p4))))) := by
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
theorem thm_5_vars_260359640412687281877676121830 : ((p2 → p5) → ((p3 ∧ ((False ∨ False) ∨ ((p1 ∨ (p3 → (True → (p5 ∨ p3)))) → (True → ((True ∧ False) ∧ p5))))) → ((p4 ∨ p1) ∨ False))) := by
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
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : (p1 ∨ (p3 → (True → (p5 ∨ p3)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h12 := h8 h9
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246617444845916875208978667454 : ((p5 ∧ p3) ∨ (((((((p2 ∧ (p5 ∧ (((p2 ∧ p1) → p1) ∧ (True → False)))) ∨ (True → False)) ∨ (p2 ∧ p4)) ∨ p2) → p5) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305288718616010023660927527902 : (p1 ∨ ((((((p5 → p5) ∧ p5) ∨ ((p2 → ((p3 ∨ (True ∨ True)) ∧ p1)) → p5)) ∨ p4) ∨ True) ∨ (p4 → (p4 ∧ (p4 → (p3 → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703127267478963248356155752122 : (((((p1 ∧ p4) → ((False ∨ p5) ∨ ((p2 ∧ False) ∨ False))) ∨ ((False ∧ p4) ∨ (True ∨ ((p5 ∧ (p5 → (False ∨ p2))) ∧ (p2 → False))))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_157542043410981080075705296735 : ((((True → (p5 ∧ ((((p1 ∧ p5) ∨ p2) ∨ (p4 ∧ (p2 ∧ p2))) ∨ True))) ∨ p1) → (p2 → p4)) ∨ ((p4 ∧ False) → ((True → p3) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196781301472388079234825389711 : ((((p1 ∨ p1) ∧ (p3 ∧ (p1 ∨ p1))) ∧ p2) ∨ ((p3 ∧ p2) → ((p5 → p2) ∨ ((p3 ∨ ((False → p4) ∧ (p5 ∧ (p3 ∧ p3)))) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177746344667992788587074801075 : ((((True ∧ True) ∧ (False ∨ (p5 ∨ (p2 ∨ ((p3 → True) → p4))))) ∧ True) ∨ (p5 → ((p1 ∧ p2) ∨ (p1 ∨ ((False ∧ (True ∨ p5)) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311826428755050264964077992991 : (p2 ∨ (p1 ∨ ((((True ∧ (p2 ∨ (((p5 ∧ p1) → True) ∧ p2))) → True) → p3) → ((False ∨ (((p1 → (p4 ∨ p4)) ∧ p4) ∨ p3)) ∧ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∧ (p2 ∨ (((p5 ∧ p1) → True) ∧ p2))) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810856062587940130325912559897 : (((p5 → ((p5 ∧ False) ∨ ((p3 ∨ (((True → (p2 ∨ p1)) → p1) → ((p2 ∨ ((p4 → p2) ∧ p4)) → ((p5 ∧ p2) ∨ p4)))) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184557211742746098434347189271 : (((((p3 → (p3 ∨ p3)) ∨ p2) ∨ (False ∨ p4)) → (p3 ∧ p2)) ∨ (p1 → (p2 → (True → ((p4 ∨ (p1 ∧ True)) ∨ ((p1 → True) ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62794029234866184393623759561 : ((p4 ∧ ((((p5 ∨ p4) ∧ (p1 ∨ ((p4 ∨ p1) ∧ p4))) → ((p5 → p1) ∧ (True ∧ False))) ∨ (p1 → ((True ∧ p4) ∨ (p5 → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732252205658897924652891361871 : ((((False ∧ True) ∧ ((p4 ∧ (((p3 → (((p4 → True) ∨ (p1 ∧ (((False ∧ True) → False) → p4))) ∧ p4)) ∧ True) → p2)) ∧ (p2 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744388241618807092337544152499 : ((((p2 ∧ True) → ((p5 ∧ (p2 ∨ p4)) ∨ (p4 ∧ ((((p1 ∧ p2) ∨ p5) ∧ (((p4 ∧ p1) → True) → ((False ∧ p4) → p1))) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704465191254774765074794339259 : ((((((p3 ∨ p1) → p4) → (p5 ∧ (p2 ∨ (p5 → False)))) → ((True → (((p5 → (p3 ∧ (p2 → (p4 ∨ p2)))) ∨ True) ∨ p4)) ∨ False)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_17968745786948382613922595504 : ((((p2 ∨ (p2 → ((p3 ∨ (p2 → p4)) → p2))) ∧ ((p5 ∨ p5) ∨ ((p2 ∨ (p5 ∧ p1)) ∧ False))) ∨ ((False ∨ (p1 ∧ True)) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_112238434494810015709387213360 : (((p2 ∨ (p3 → (((True → (p3 → p4)) ∨ (((p4 ∧ p3) ∨ (p1 ∨ (p4 ∧ (False ∨ p2)))) ∨ p5)) ∨ (True → p5)))) ∨ True) ∨ (p4 ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184706264628258722091373357752 : (((((p5 → p5) ∨ p1) ∨ (False ∧ True)) → (p1 ∧ (p5 ∨ p1))) ∨ (False → (p5 ∨ ((False → True) ∨ (p1 → (((p1 → p5) ∧ p5) → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301793725244991116891859130630 : (False ∨ ((p3 ∧ p3) ∨ ((False → (p4 ∧ (False → p4))) ∧ ((p2 ∨ True) ∧ (((((True ∧ p5) ∧ (p3 ∧ True)) ∧ p3) ∨ p3) ∨ (False → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305510646394329254213762323373 : (p1 ∨ ((p5 ∧ (p5 ∨ ((p3 → p4) → ((p1 → (False → (False ∨ p4))) → False)))) ∨ (((False → p1) ∨ False) → (((False ∧ p1) ∨ True) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124081067585586653309851849071 : (((True → (p3 ∨ ((p5 ∨ (False ∧ ((p3 ∧ p2) ∧ p2))) → p5))) → ((((p1 → False) ∧ (p3 ∧ p4)) ∨ (p3 → p2)) ∧ False)) → (p1 ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → (p3 ∨ ((p5 ∨ (False ∧ ((p3 ∧ p2) ∧ p2))) → p5))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661662448007154211428754499416 : ((((((p5 → False) → ((((p1 → p5) ∨ (((p3 ∨ p1) ∧ (p4 ∧ p4)) → p5)) ∨ p2) ∨ p3)) → (p2 → (p4 ∧ True))) → (p5 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50086597290263328673348265460 : (((p1 ∧ ((p3 ∨ ((False → False) ∧ p2)) ∧ (p2 → ((False ∨ p1) ∧ (True → ((p2 → True) ∨ p5)))))) ∧ (((p3 ∨ p4) ∨ True) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122070538920336025458706702717 : (((p3 → (((p1 ∨ p1) ∨ ((p2 ∨ (p5 → (((p4 ∧ ((p5 → p5) ∨ (p4 ∧ p3))) ∧ False) ∧ p1))) → True)) ∧ True)) → False) → (False ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → (((p1 ∨ p1) ∨ ((p2 ∨ (p5 → (((p4 ∧ ((p5 → p5) ∨ (p4 ∧ p3))) ∧ False) ∧ p1))) → True)) ∧ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p3 → (((p1 ∨ p1) ∨ ((p2 ∨ (p5 → (((p4 ∧ ((p5 → p5) ∨ (p4 ∧ p3))) ∧ False) ∧ p1))) → True)) ∧ True)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h6
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310159819937589394550629395814 : (p2 ∨ (((True ∧ True) → (((((p1 → p4) ∧ False) ∧ (p2 ∧ p1)) ∨ p2) ∧ False)) → (p5 ∨ (p2 ∧ ((False → (True ∧ (p1 ∧ p2))) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157208282539230712069556358249 : ((((((((p3 ∧ p2) → p5) → (p5 ∧ p1)) → False) ∧ (p3 ∧ (p5 → p5))) → (p1 ∨ p2)) → p2) ∨ (False → (p5 ∨ (False → (p5 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205162397557412863872824743341 : (((p3 ∧ (p4 ∨ p1)) ∧ (p2 ∨ p4)) ∨ ((p2 → ((p2 ∨ True) ∧ True)) ∨ ((p2 ∧ False) ∨ (True ∧ (((p2 ∨ False) ∧ False) ∨ (p5 → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191916503880811515434673737318 : ((p5 ∨ (p4 ∨ (p2 ∨ (p1 → (False ∨ (p3 ∨ True)))))) ∨ (True ∧ (p4 ∧ (p3 → (((p5 ∧ (p5 ∧ (p4 ∧ p5))) → (False ∧ p5)) ∨ p2))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191457899264682447861824379098 : (((p3 → p3) → (p2 ∧ (True → ((False ∧ p1) ∧ p2)))) ∨ (p5 → (((((p4 → p2) ∨ False) → (False ∨ ((False → True) → p5))) ∧ p1) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158729680664922593014392915909 : ((p3 ∧ ((p3 → p2) → ((p2 ∨ (p4 → False)) → (((False ∨ p1) → ((p4 ∨ p5) ∨ p4)) ∧ p1)))) ∨ (p1 ∨ ((p1 ∨ (p5 → p5)) ∨ p2))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64567522196706321349819133181 : ((p1 ∨ (((False ∧ p1) ∧ True) ∨ (((((p1 → p2) ∧ p5) ∨ (p1 ∨ True)) → (p1 ∧ (p4 ∨ (True ∧ (False → (p2 ∧ False)))))) → p1))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 → p2) ∧ p5) ∨ (p1 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51466036092542596735655528898 : ((((((False ∧ p1) ∨ False) ∧ ((True ∨ p4) ∨ (p3 ∨ p3))) → ((p2 ∨ (p3 ∨ p4)) ∨ False)) → ((p2 → p3) ∨ (p2 → (p2 → p2)))) ∨ p2) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143944871365701623886050963707 : (((((p4 ∨ p1) ∨ (p3 → p1)) → (p2 ∨ (p1 ∧ (True ∧ ((((p3 → p1) ∨ False) ∧ True) ∨ True))))) ∨ True) ∧ (False → ((p4 ∧ p3) ∨ True))) := by
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
theorem thm_5_vars_198763076850498320074340744367 : ((True → (False ∧ (False ∧ ((p3 → p4) → p1)))) ∨ (((p5 → False) ∨ (p4 → (((True → p3) → ((p4 ∨ True) ∨ p4)) → p5))) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22166696555360519640461053350 : ((((False ∨ False) ∨ (p2 ∨ ((p3 → False) ∨ False))) ∨ ((p2 ∧ True) → ((p1 ∨ p2) ∨ (p5 ∨ (True ∨ (((p1 → p4) ∧ True) → p1)))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653805922649323567546558433046 : ((((((p3 ∧ ((False ∧ ((p3 → (p4 ∧ (p5 → p1))) ∨ p3)) ∨ p5)) ∧ (p2 ∨ (((p1 → p3) ∧ True) ∨ True))) ∧ p4) ∨ (p2 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



