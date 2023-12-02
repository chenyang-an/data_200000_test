variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710889506938650413382108635927 : (((((False ∧ False) ∨ ((True ∧ p4) ∨ False)) ∧ ((((p2 → (False ∨ ((True → (p2 → p2)) → p5))) ∧ False) ∨ (p2 → p5)) ∧ (p3 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_942573425456323690742924137073 : ((((((p1 ∧ p4) ∨ False) → p5) ∧ (((False ∧ p4) ∨ ((p4 → p2) → ((True → (p2 ∧ p2)) → (p1 → ((p2 ∧ p2) ∧ p1))))) → False)) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∧ p4) ∨ ((p4 → p2) → ((True → (p2 ∧ p2)) → (p1 → ((p2 ∧ p2) ∧ p1))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- One of the premise coincides with the conclusion.
    exact h10
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h12 := h6 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- One of the premise coincides with the conclusion.
    exact h13
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h14 := h3 h4
  -- False on the left can always be used.
  apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113581429401084563557110263241 : (((p1 ∧ ((p3 ∧ p2) ∨ (p5 → ((((((p4 ∧ p5) ∨ p5) ∧ p4) ∨ False) → ((p1 → p2) ∧ p4)) ∨ p2)))) ∨ (p4 → p2)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791996868935906080133659976542 : (((True → ((((((p1 → (p2 ∨ p2)) ∧ (False → False)) ∧ p2) ∨ (p5 ∨ (p5 ∨ p2))) ∧ (True ∧ (True ∧ (False → p1)))) → (False ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164759136232559695918318388760 : (((((p4 ∨ ((True → (True → True)) → (p1 ∨ p4))) ∧ p1) ∨ ((p1 → False) ∨ True)) ∨ p3) ∨ ((((p1 ∨ True) ∨ False) → (p1 ∨ False)) ∧ p3)) := by
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
theorem thm_5_vars_111274285711397075907900838722 : ((((p3 ∧ p5) → (((p1 → ((p1 ∧ True) → ((False ∧ (p2 ∧ p3)) ∧ True))) → (p4 ∧ (p2 ∨ True))) ∨ (False → p4))) ∧ True) ∨ (False ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305805298445128917252952117548 : (p1 ∨ ((((p2 ∧ False) ∨ False) ∨ ((True → False) ∧ p3)) → (True ∧ (((p4 ∨ p5) ∨ (False ∨ (((False → False) → (False ∧ p5)) → p4))) ∧ p4)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h20 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h21 := h18 h20
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153373328883440218770302007825 : ((p2 ∨ (False → ((((p4 ∨ (p4 ∧ (((p5 ∧ False) ∧ (p1 ∧ (False ∨ p1))) ∧ True))) → p2) ∧ p4) ∨ p3))) → (((True → p3) → p1) ∨ True)) := by
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
theorem thm_5_vars_218908740793617696268866191328 : ((p3 ∧ ((p5 → p3) ∨ p1)) → (p4 → (((p2 ∧ p5) → (True → p4)) → ((((p4 → (p3 ∧ (p3 ∧ p1))) → (p2 ∨ p1)) ∨ p1) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309318060775219460937402011227 : (p2 ∨ ((((((p4 ∨ (p2 → (p1 ∧ p2))) → (True ∨ p4)) ∧ ((p1 → (p4 → (p1 ∧ (p4 ∧ p1)))) ∧ p3)) ∧ True) → p1) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57360131752812005630882448584 : (((p3 ∧ (p4 → p1)) ∨ (p5 → (((((p2 ∨ (False ∨ ((p4 ∧ p5) → (False → p5)))) ∨ (False ∧ True)) → False) ∨ p2) ∨ (False → p2)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116507928121076431269371198521 : (((p4 ∧ p1) ∧ (((((p2 → p4) ∧ ((False → p4) ∨ p2)) → (p4 → p1)) ∧ p1) ∧ (p5 → (((p5 ∨ p3) ∨ False) ∨ p2)))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_909534003810912501167724421109 : (((((p5 ∨ True) → ((((p3 ∧ True) → p2) ∨ ((((p4 → p3) ∨ True) ∨ p5) ∨ p5)) → False)) ∧ ((((p1 → False) ∨ True) ∨ True) ∨ True)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h7 : (p5 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h8 := h2 h7
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h9 : (((p3 ∧ True) → p2) ∨ ((((p4 → p3) ∨ True) ∨ p5) ∨ p5)) := by
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
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h10 := h8 h9
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h12 : (p5 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h13 := h2 h12
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h14 : (((p3 ∧ True) → p2) ∨ ((((p4 → p3) ∨ True) ∨ p5) ∨ p5)) := by
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
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h15 := h13 h14
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h17 : (p5 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h17
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h19 : (((p3 ∧ True) → p2) ∨ ((((p4 → p3) ∨ True) ∨ p5) ∨ p5)) := by
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
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h20 := h18 h19
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h22 : (p5 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h23 := h2 h22
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h24 : (((p3 ∧ True) → p2) ∨ ((((p4 → p3) ∨ True) ∨ p5) ∨ p5)) := by
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
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h25 := h23 h24
    -- False on the left can always be used.
    apply False.elim h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167887558487635680644276444356 : (((False → ((False ∨ (False ∧ ((p1 ∧ p5) ∨ p4))) → p1)) → (p2 → (p3 → (p1 ∧ True)))) → (((True → False) ∨ (False → (False ∨ False))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641280205224192160472594815801 : (((((True → p1) ∨ (p5 ∨ (p2 → (((p2 ∨ p2) ∨ p3) ∨ ((p2 ∧ p2) → ((p5 ∧ p2) ∨ ((p1 ∨ False) ∨ (False ∧ p5)))))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56739470505925923176737977820 : ((((p5 ∨ p4) ∨ p4) ∧ (False ∧ (((p5 ∧ p5) ∨ p2) → ((((p4 ∨ (p3 → p4)) → ((p4 → (False → p1)) ∨ False)) ∨ p4) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234856223019328435466130352688 : ((p5 → (False → True)) → (((p4 ∨ p2) ∧ ((p5 ∧ (p1 ∧ (False ∧ False))) ∨ ((((p4 → p5) ∧ (True ∧ p2)) ∧ (p4 ∨ p2)) ∧ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49924093817344107422273574677 : (((((False → p2) ∧ (p4 ∧ (((p2 → p1) ∧ (p5 ∨ ((p1 → p3) → p5))) → (True → p1)))) → p3) ∧ (((p3 ∨ p3) → True) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159030581323194968565598841787 : ((p4 ∨ (p2 ∧ (((p1 ∨ (True ∧ ((p4 ∧ False) → (p3 ∨ p5)))) ∧ p4) → ((False → p5) ∧ p5)))) ∨ (((p2 → p5) ∧ False) → (p4 ∨ p1))) := by
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
theorem thm_5_vars_166537017652201267110802193911 : ((p5 ∨ ((((p3 ∧ ((False → p4) ∨ p1)) ∨ (False ∨ p1)) → (p3 ∧ (p1 ∨ p1))) ∧ p5)) ∨ (((True ∧ p5) ∨ True) ∨ (p5 ∧ (p4 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157678868619593455442759503400 : ((((p5 ∨ p5) → (p1 → (((True ∧ (p2 ∨ (p2 → False))) ∧ p2) ∧ True))) ∨ (False → (p2 ∧ False))) ∨ ((p5 ∧ (p2 → (True ∨ False))) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_741673250362533870470604335478 : ((((True → False) ∨ ((p2 ∧ p3) ∧ (((((((p3 → p1) ∧ ((False ∨ (p5 ∨ p5)) ∨ (p3 ∧ p1))) → True) ∧ p4) ∧ True) ∨ p3) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115662710354445834786625252074 : ((((True ∧ p4) ∧ ((True ∧ p2) ∧ True)) ∨ (((False → p2) → (False ∨ (p3 ∨ (((p3 ∨ p4) ∧ False) ∨ p4)))) ∨ (True ∨ p5))) ∨ (True → p2)) := by
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
theorem thm_5_vars_51729463405375978394061776922 : (((((True ∨ (p1 ∨ True)) ∧ p1) ∨ ((p4 ∧ (False ∧ p5)) ∧ ((p2 ∧ p3) ∧ p3))) ∧ (((p1 ∨ ((True ∨ True) → True)) ∨ p1) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116326310503705900874091992208 : ((((True ∨ p4) ∧ p5) → (p2 → ((((True ∧ ((p4 → p4) ∨ (True ∨ p5))) → (False ∨ (p3 → p4))) ∨ p4) ∨ (True ∧ False)))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233532597402513759882363662159 : ((p1 ∨ (p2 ∨ p3)) → ((p3 ∨ ((((p5 ∨ ((p2 ∧ (False → p1)) ∧ False)) ∨ p5) ∨ p5) ∨ (p2 ∧ p2))) ∨ (p5 ∨ ((p3 ∧ p5) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209135086207525261540393688818 : ((p3 ∨ (((p1 ∧ p4) ∧ p5) ∨ False)) → (((p5 → ((((p3 ∧ True) ∨ p1) → ((((p5 ∨ p1) ∧ p2) ∧ p3) ∨ p2)) ∨ p3)) ∨ p5) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806227883883756325576552902284 : (((p4 → (((True ∧ ((((p3 ∨ ((False ∧ ((p1 → p3) ∧ (False ∧ True))) → (p3 ∧ p5))) ∨ p3) → p5) ∧ p2)) ∨ (p3 ∨ p1)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170024812999477677629861868267 : (((((p2 ∧ p5) ∨ (False → p3)) ∧ ((p2 ∨ p1) ∧ p2)) ∨ (True ∨ (True → False))) ∧ ((False ∨ ((True ∨ p1) ∧ False)) → ((p4 ∨ True) → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h7
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- False on the left can always be used.
        apply False.elim h14
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83045755904742891989954482458 : (((((p3 ∨ p2) ∨ (p5 ∨ p5)) → ((p1 ∧ p5) → (((p4 ∧ ((p2 ∧ p5) ∨ p1)) ∧ p4) ∨ p1))) → ((True ∨ (p4 ∧ True)) → False)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 ∨ p2) ∨ (p5 ∨ p5)) → ((p1 ∧ p5) → (((p4 ∧ ((p2 ∧ p5) ∨ p1)) ∧ p4) ∨ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h2
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h14 : (True ∨ (p4 ∧ True)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h15 := h13 h14
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184511421465687299798954466719 : (((False ∧ (p4 → (False ∨ (p2 ∨ (p5 ∨ p5))))) ∨ (p5 ∨ p3)) ∨ (((p5 ∧ ((p5 ∧ (p4 ∧ (p1 ∧ (p4 → p2)))) ∨ p2)) → p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68094402276434364119878210400 : ((p2 → (True → ((p2 ∧ (((p5 ∨ (((p3 ∧ p4) ∨ p4) ∧ (p3 ∨ p4))) ∧ (((p5 → p1) → p1) → p1)) ∨ True)) ∨ (p4 ∧ p2)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353474443400996919963914428607 : (p4 → (p2 ∨ ((p1 ∧ (p5 → (p2 ∧ (p1 ∨ (((p2 ∨ p1) ∨ True) ∧ ((p1 ∧ (((True ∨ (p4 ∨ p5)) → False) ∨ p4)) → p1)))))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638410085601710260273431148334 : (((((False ∨ (p5 → ((True → p2) ∧ p4))) ∧ (p4 ∨ ((((((p5 → (False → p3)) ∨ False) ∧ p5) → True) ∨ (True ∨ False)) ∨ False))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308371280913035638577899311636 : (p2 ∨ (((((p5 → (((False → p5) ∨ p5) → ((p4 ∧ ((p2 → ((p3 ∨ p1) ∧ (p5 → True))) → True)) ∨ p4))) → p2) ∨ p1) ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783280432878411551852249476289 : (((p3 ∨ ((((((((p3 ∧ False) ∧ (p5 → p2)) ∨ p4) ∨ p2) ∨ ((p5 ∧ True) → p2)) → p2) ∨ p4) ∨ ((False ∧ p1) ∨ (p2 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185391951405225381183785927154 : ((p5 ∧ (p5 ∨ (((p1 → (False → (False ∧ False))) → p3) ∧ p5))) ∨ ((p1 ∧ p4) ∨ ((True ∨ ((p2 ∨ (p4 → False)) → p5)) ∨ (p5 ∧ p1)))) := by
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
theorem thm_5_vars_300673210397025763151049564368 : (False ∨ (((p1 ∨ ((p1 ∨ ((p5 ∨ p3) → (p1 ∧ ((p2 ∧ p3) → p2)))) ∨ True)) ∧ (True ∧ p1)) ∨ (True → (p2 → (p5 ∨ (p2 ∨ p5)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227981764180324941063285785777 : ((p3 ∧ (p2 ∨ p2)) ∨ (((((p2 ∨ p2) ∨ p5) ∧ p5) → ((p4 → (p5 ∧ (False → False))) → (p3 ∨ True))) ∧ (((False ∨ p1) ∨ p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
  -- Implications on the right can always be decomposed.
  intro h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257671792401163784625192838266 : ((p3 ∨ p3) → (((p5 → ((False ∨ ((p3 → p4) ∨ (p2 ∨ p1))) ∨ (p3 ∧ False))) ∨ (False → (p1 ∧ ((p1 → p3) → (p3 ∨ p2))))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117523937982126767291031541983 : ((p2 ∧ (((p2 ∨ (p3 → ((p3 ∧ (False ∧ (False ∨ (p4 → (p5 ∧ p3))))) → (p2 → p4)))) ∨ ((p1 ∧ True) ∧ p2)) → p4)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135872162661126747640421186361 : (((((p1 ∧ p3) ∧ (p1 ∨ p2)) → (p4 ∧ ((False → p1) → p2))) ∨ ((False → (p1 ∧ p5)) → (p4 → (p5 ∨ p3)))) ∨ ((False → p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734951868164199449281749813771 : ((((p2 ∨ p4) ∧ (p4 ∨ (((p4 ∨ p4) ∧ (((True → p5) → p5) ∨ (False ∨ p3))) ∨ ((p1 ∧ ((p1 ∨ True) ∨ (p5 → p1))) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314006940072425838249459804209 : (p3 ∨ ((p1 ∧ (((((((p3 → p1) ∧ (True ∨ (p3 ∧ True))) ∨ p1) ∧ p5) → p1) ∨ ((p1 ∧ (p3 ∧ False)) ∧ p3)) ∨ p5)) ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147381245167672252009920054036 : ((((((False ∨ p5) ∧ (True ∧ p2)) ∨ ((p1 → p5) → p2)) ∨ (p2 → (False → ((p5 → p3) → p4)))) ∨ p3) ∨ (False → (p4 ∧ (True → p5)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59866784744499942939621974467 : (((p4 ∧ p1) → (p2 → (((((p4 ∧ p1) → ((True → p2) ∨ p3)) → ((p5 ∨ p2) ∧ (((p5 → p4) ∧ True) ∨ p4))) → p2) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149705514467453515564503992763 : ((p5 ∧ (True ∧ (((p1 ∨ True) → p4) ∨ ((p3 → p4) ∧ (((p3 ∨ (True → p4)) ∨ p1) ∧ (p1 ∨ p1)))))) ∨ ((False ∧ True) → (p1 → False))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117429501888675140040092534238 : ((p1 ∧ ((p2 ∧ (p2 → (((p1 ∧ (p5 ∨ False)) ∨ (False ∧ ((p4 ∧ p3) ∧ p5))) ∧ True))) ∨ (True ∨ (p1 ∧ (p5 ∧ p5))))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192095999008779538307261814698 : ((p4 → ((p3 ∧ (False ∧ (True → p2))) ∨ (p2 ∧ True))) ∨ (True ∧ ((p3 ∧ (False ∨ (p1 ∨ (True ∧ ((p5 ∨ (True ∨ p1)) → p3))))) ∨ True))) := by
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
theorem thm_5_vars_181528999488314975593287180591 : ((True → ((p3 ∨ (((p3 ∨ True) ∨ p1) → True)) → ((p2 ∨ p5) → False))) → (((p1 → p5) → p2) ∨ ((False → (True ∨ True)) ∨ (False ∨ True)))) := by
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
theorem thm_5_vars_61615723062891866383906005272 : ((p1 ∧ ((False ∧ True) ∨ (((((((((True ∨ p5) ∨ (True → (True ∨ p2))) → p4) → p1) ∨ (p2 ∨ p1)) → p3) ∨ False) ∧ True) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248883807087224816452936148690 : ((p3 ∨ p5) ∨ ((p2 → (p1 ∨ ((p4 ∨ ((p1 → False) → p5)) ∨ ((p2 → (p2 ∧ p5)) ∨ (p3 ∧ p1))))) → (((p1 → p5) ∨ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311787328722750001515572990000 : (p2 ∨ (False ∨ (p1 ∨ ((p3 → p5) → (((p3 ∧ ((p4 → ((p1 → False) → ((p2 ∧ (p2 ∧ p5)) ∨ p1))) ∧ p4)) ∧ (p4 ∨ p3)) ∨ True))))) := by
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
theorem thm_5_vars_166718566872468189463360838144 : ((p3 → ((p5 ∨ p1) ∧ ((p2 → (False ∧ ((p2 ∨ p5) ∨ (p5 ∨ (p1 ∧ p5))))) → p2))) ∨ (p3 ∨ (p2 ∨ ((False → False) ∨ (p1 → p5))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62979213164270550084186115853 : ((p4 ∧ (p3 ∨ (p2 ∨ (((((p2 ∨ (True ∧ p4)) ∧ ((p1 → p1) → p1)) ∨ p3) → (((True ∧ p4) → p5) ∧ (p4 ∨ False))) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219812875757377063378592165929 : ((p3 → ((True ∧ p1) ∧ p3)) → (((p5 ∨ ((True ∨ ((p3 ∧ (p1 ∧ p1)) ∧ False)) → True)) → (((p1 ∧ (p3 ∧ False)) ∨ True) ∨ p1)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148103283773640120016249927237 : ((((p4 ∧ ((((p2 → (p4 ∧ False)) ∨ True) ∧ ((p3 → False) ∧ p1)) ∨ p2)) → (p1 ∨ p1)) → (p5 → p2)) ∨ (True ∨ ((p3 ∨ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116099670998823624896035937069 : ((((p5 → p2) ∨ p5) ∧ ((p3 ∧ p1) ∧ (p3 → ((True ∧ False) ∧ ((p4 → p3) → ((((p2 ∧ False) → p3) → p2) ∧ True)))))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247732416335375179108763527861 : ((p1 ∨ False) ∨ ((p4 → ((p5 ∨ (p1 ∨ p3)) ∨ ((p2 ∧ p3) ∨ ((p4 → p3) ∧ p1)))) ∨ (((p2 → (p1 ∧ True)) ∧ (p2 ∨ p1)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52076541531211369252698284874 : (((((p4 ∧ p3) ∨ (p5 → (((p1 → (True → True)) → (p4 → p3)) ∧ p3))) ∧ p1) → ((p4 → ((True → False) ∨ p4)) ∨ (p5 ∨ True))) ∨ p3) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
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
theorem thm_5_vars_37859987102929755548206147404 : ((((p2 → ((True → (True ∧ (False → p2))) → ((False ∨ True) → (((((p4 → p2) ∨ p1) → p1) ∨ (p2 ∨ p2)) → p3)))) → p5) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135130765282629902698674824052 : (((p3 ∧ (((p1 ∧ (p1 ∧ ((((True ∨ False) → p4) → p3) → p2))) → True) → ((p3 ∧ True) ∨ p2))) ∨ (True ∨ p2)) ∨ (p4 → (p2 ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51292392318636650115208999871 : (((p5 ∧ (((p1 ∧ (((p1 ∧ p5) ∨ (p5 → (p4 ∨ (True → True)))) ∨ p4)) ∨ True) ∨ p5)) ∨ ((False ∧ p5) → (p3 → (True ∨ p5)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310940821331319267788808603547 : (p2 ∨ ((False ∨ True) ∧ ((((((p2 ∧ ((p5 → p3) ∧ False)) ∧ False) ∨ ((True → (p4 → p2)) ∧ p5)) ∧ (p1 ∨ p4)) ∧ p4) → (p2 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h16 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h18 := h14 h17
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h19 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h20 := h18 h19
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h22 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h23 := h14 h22
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h24 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h25 := h23 h24
      -- One of the premise coincides with the conclusion.
      exact h25
  -- Conjunctions on the left can always be decomposed.
  let h26 := h1.left
  let h27 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h28 := h26.left
  let h29 := h26.right
  -- Disjunctions on the left can always be decomposed.
  cases h28
  case inl h30 =>
    -- Conjunctions on the left can always be decomposed.
    let h31 := h30.left
    let h32 := h30.right
    -- Conjunctions on the left can always be decomposed.
    let h33 := h31.left
    let h34 := h31.right
    -- Conjunctions on the left can always be decomposed.
    let h35 := h34.left
    let h36 := h34.right
    -- False on the left can always be used.
    apply False.elim h36
  case inr h37 =>
    -- Conjunctions on the left can always be decomposed.
    let h38 := h37.left
    let h39 := h37.right
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h40 =>
      -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
      have h41 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h38, we can now drive its conclusion.
      let h42 := h38 h41
      -- We want to use the implication h42 based on <expert-advice>. So we show its premise.
      have h43 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h27
      -- We have shown the premise of h42, we can now drive its conclusion.
      let h44 := h42 h43
      -- One of the premise coincides with the conclusion.
      exact h44
    case inr h45 =>
      -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
      have h46 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h38, we can now drive its conclusion.
      let h47 := h38 h46
      -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
      have h48 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h27
      -- We have shown the premise of h47, we can now drive its conclusion.
      let h49 := h47 h48
      -- One of the premise coincides with the conclusion.
      exact h49



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171596915529881441016742536715 : ((((p3 → (p5 → (p4 → (p3 ∧ (p2 → p3))))) → ((True ∧ p5) ∨ p4)) ∨ True) ∨ (((True ∨ ((p4 → p2) ∧ p2)) → (False ∨ False)) → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46727890714357651754702850628 : (((True → (((((p4 ∧ p4) → (p2 ∨ p4)) → p3) → (p1 ∧ p4)) ∧ (False ∧ ((((True → p4) → p3) → p5) ∨ p4)))) ∧ (p4 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47900228737251468318706362474 : ((((p1 → (False → (p1 → ((True → p2) → ((((True ∨ p4) → True) ∧ p5) → (p3 ∧ (p4 → False))))))) ∨ (p4 ∧ p2)) → (False ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262518787937174406884274432758 : (True ∧ ((p5 → ((((p3 ∨ (p5 ∧ p4)) → (((True ∨ (True → p4)) ∧ False) ∨ p1)) ∨ p4) → (p5 → (False ∨ ((p4 → p1) ∨ p5))))) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327823233489319067018028046591 : (True → (((p4 ∧ (p5 ∧ ((p3 ∧ ((p5 → False) ∨ p5)) → ((p4 ∧ ((True ∧ (p4 ∨ False)) → False)) ∨ False)))) ∧ (False ∧ False)) ∨ (True ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45041593126281582836214056330 : ((((p5 ∨ p1) ∨ (p1 → (True → (((True → ((((False ∨ p2) ∨ p3) ∨ p5) ∨ p2)) ∨ p3) ∨ (False ∧ ((p1 ∧ p2) → False)))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185934986582441262173257236717 : ((((False ∨ (p5 ∨ p1)) → (((p5 → p4) ∨ p1) ∨ p5)) ∧ p3) → ((True → p5) ∨ ((True → (p4 ∧ (False ∧ p2))) → ((p5 ∨ p3) ∧ p2)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346357486240458018618234729355 : (p3 → (((p4 ∨ p5) ∧ ((True ∧ p5) ∨ ((True → (p2 ∨ p4)) → (((p1 → p4) ∧ p1) → (((True ∧ p4) ∧ p5) ∨ False))))) ∨ (True ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300099079044560075990838405508 : (False ∨ (((((p1 ∨ True) ∨ ((True ∨ p5) → False)) ∧ ((p5 → p2) ∨ ((False ∧ p1) ∧ False))) ∨ (p3 → ((True ∨ p4) ∨ p2))) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204094512459518217948529350526 : ((p5 → (p5 ∨ ((p2 ∨ False) ∧ False))) ∧ (((p2 ∨ (p3 → p2)) → ((p1 ∨ p2) ∧ (((p5 ∧ (False ∧ True)) → (p5 ∧ p4)) ∧ False))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1769938142104010801989193848 : (((((((p1 ∧ p5) → p3) ∧ ((p1 → (p3 ∧ False)) → (True ∧ False))) ∧ (True ∨ (p1 ∨ p3))) ∧ p4) → False) ∨ ((p1 → p1) ∧ True)) := by
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
theorem thm_5_vars_56942968975818346727494521508 : (((p1 ∨ (False ∧ p2)) ∧ (p3 → ((((p5 ∨ ((True ∧ (((p5 → True) → p2) ∨ (p4 → (p4 ∨ True)))) ∨ False)) ∨ p3) ∨ False) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215751246320049069590214151226 : ((p1 ∨ ((p2 ∨ p1) ∧ p1)) ∨ (True → ((p2 ∨ (p5 ∧ ((True ∧ p1) → p5))) → (p5 ∨ (((False ∨ p5) → True) ∨ ((p2 → p4) ∧ True)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257298121978218361767802102566 : ((p2 ∨ p3) → (p4 → (p4 ∧ (((True → False) ∧ ((((p4 ∧ False) ∨ p4) ∧ True) ∧ p3)) ∨ ((p3 ∨ (p3 ∧ (p4 ∧ True))) → (p4 ∧ True)))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h11
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- One of the premise coincides with the conclusion.
      exact h19
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303884814143364284976149955797 : (p1 ∨ (((((((p1 ∨ p1) ∨ p2) ∧ (p5 ∧ False)) ∨ (True ∨ True)) ∧ (False → ((True ∨ p3) ∧ False))) → ((p2 → p1) ∧ (p2 ∨ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204571230241761671166116507701 : ((((p3 ∨ p1) ∧ (p4 ∨ p3)) ∨ p2) ∨ (((p1 → False) ∨ ((((p2 → p2) ∧ False) ∨ p3) ∨ (False ∨ ((p5 ∧ p2) ∧ p1)))) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205858047853394076581237407331 : (((p4 → p2) → ((p3 ∨ p4) ∨ False)) ∨ (p3 ∨ ((((p5 ∨ (((p5 → p2) ∨ p5) ∧ ((p3 ∧ p2) ∧ p3))) → False) → (p5 ∨ p2)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76501304671461622279838096702 : ((((p1 → ((p5 ∨ ((((p1 → (p5 ∧ False)) ∨ p2) → (p5 → p4)) ∧ p1)) → ((True → p5) ∨ p4))) ∨ ((p4 ∧ True) ∨ True)) → False) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 → ((p5 ∨ ((((p1 → (p5 ∧ False)) ∨ p2) → (p5 → p4)) ∧ p1)) → ((True → p5) ∨ p4))) ∨ ((p4 ∧ True) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672731359374110237842275062862 : (((((((((p1 ∨ (p2 ∨ p5)) ∨ (p4 ∧ p5)) → p3) → ((p3 → p5) ∧ p2)) ∧ (p5 ∨ p4)) → (p1 ∧ p3)) → (p1 → (p3 ∨ p1))) ∨ p3) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307365825139866791077219311333 : (p1 ∨ (p4 ∨ ((False ∨ ((p3 ∧ (p3 ∨ (True ∧ (((p2 ∨ False) ∧ ((True ∨ p4) ∨ (((p5 → p5) ∨ p1) ∧ False))) ∨ True)))) → p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209419514105587079192352714729 : ((p2 → ((True ∨ (p4 ∨ p4)) ∨ p4)) → (p3 ∨ (((p1 ∧ p1) ∨ (((((p3 → p2) ∧ p4) ∧ ((p4 → p5) ∧ False)) ∧ p4) ∧ False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111183570116323815712206348868 : (((((p4 ∧ p4) ∨ (p2 → False)) → ((p1 ∨ (p1 → ((p4 ∨ (False → p4)) ∧ (p4 ∨ True)))) → (True → (p5 ∧ p5)))) ∧ True) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67430837113242347143074361105 : ((p1 → ((True ∨ (((((p1 ∨ ((True ∧ (p2 ∨ p5)) → (p4 ∨ p4))) ∨ p1) → (True ∧ p1)) ∧ p2) → (p3 ∨ p4))) → (p4 ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41704559998932807728916948921 : (((((True → p5) ∨ (p4 ∧ (p3 ∧ p3))) → (False ∨ (((((True → p1) ∧ (p4 → (True → p2))) ∨ p1) ∨ (p5 ∧ True)) ∨ p3))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49632017690011853298864350213 : (((((((p1 → p4) ∨ True) ∧ True) ∨ False) → (p2 → ((False → p2) ∨ ((False ∧ p3) → ((False ∧ p3) ∨ p3))))) → ((p5 ∧ p5) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111977155762499067011054460911 : (((((p2 ∨ p3) ∨ ((p1 ∧ p5) ∨ p5)) ∨ ((False → (p4 ∧ ((p4 ∧ ((False → True) ∨ p3)) ∨ p5))) → (False → p1))) ∨ p1) ∨ (p3 ∨ p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251535091346749273180821482744 : ((p3 → False) ∨ ((p1 → (p2 → (p2 ∧ ((((p5 → True) ∨ ((p1 → p4) ∨ (p1 ∨ (p3 ∧ p1)))) ∧ True) → ((False ∨ p1) ∧ True))))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215258122494324366789079483561 : ((False ∧ (p4 ∧ (p4 ∧ False))) ∨ (((True ∧ p5) → p3) → (p1 → ((p4 ∧ (p4 ∨ (p4 ∧ ((p2 → (False ∧ p5)) ∨ (True ∨ p1))))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54346737027459224309620440789 : (((False ∨ (p3 ∧ (((p5 ∧ p3) ∧ True) → p3))) ∧ ((p3 ∨ (True ∨ p4)) → ((p5 ∧ (p3 → p4)) ∨ ((p5 ∨ p5) ∧ (p2 ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214553998798798698936160732317 : (((False ∨ p5) ∧ (True ∧ p4)) ∨ ((p5 ∧ ((p3 ∧ ((p2 ∨ p5) ∧ (p5 → ((p2 ∧ False) → p2)))) ∨ False)) ∨ (False → (p3 ∨ (False ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159857027506791664494952183355 : (((p4 → ((p2 → p2) ∧ (((p2 ∧ p3) → True) ∧ (p3 ∨ ((p4 → (p5 ∧ True)) ∧ p4))))) ∨ p5) → (p4 ∨ ((p2 ∧ (False ∨ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37973449275011218675186258744 : (((((p2 → ((p4 ∨ ((p4 ∨ (p5 ∨ p3)) → p1)) → (((p3 → (p5 ∨ p2)) ∨ False) → p4))) ∧ (p4 ∧ True)) ∨ (p5 ∨ p1)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51218385070267764273582190903 : ((((((False ∧ (p5 ∨ p1)) ∨ p5) ∧ p4) ∨ (p1 → ((True ∧ (False → p2)) → (p4 → p4)))) ∨ (((False → p2) → (p4 ∨ p2)) ∧ True)) ∨ p5) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215118246606946397440949478318 : (((p3 → True) → (False ∨ p3)) ∨ ((p3 ∨ ((p4 ∧ (p1 ∧ p5)) ∧ (p1 ∧ (((p5 → True) ∧ True) ∨ ((p5 ∨ (p1 ∧ False)) ∧ p1))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196540846838676893640825032463 : ((p3 → ((p3 ∨ ((p2 ∧ False) ∧ p2)) ∨ p3)) ∧ ((((p3 → p4) → p4) ∧ ((p5 → (False ∧ (p1 → p1))) ∨ (p2 ∧ (p3 ∧ p3)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64531286748415115239804030096 : ((p1 ∨ (((False ∧ (True ∧ (p1 ∨ (True ∧ p5)))) ∨ p4) ∨ (p2 ∧ ((p2 ∧ ((p2 ∨ p1) ∧ (((p2 → True) → p2) → True))) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



