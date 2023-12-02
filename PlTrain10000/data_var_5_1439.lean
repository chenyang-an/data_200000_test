variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45577611288299164672926280785 : (((p2 ∨ (p2 → ((p5 ∨ (p4 ∨ ((((p5 → p5) ∧ p1) ∨ (p1 ∨ p4)) → ((False → (p2 ∧ False)) ∧ (True ∧ p2))))) → p4))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155119671530913522486655410193 : (((((p3 ∧ (p1 ∧ (p3 ∧ (False ∧ True)))) ∨ p5) ∧ p2) ∨ ((p1 ∨ (p2 ∨ (p5 → p3))) ∨ True)) ∧ (((p4 ∧ False) ∧ True) → (True ∧ True))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208267684671674531366535254950 : (((True ∨ False) ∧ (p4 → (True ∨ p5))) → ((p4 ∨ ((p3 → (((p5 → True) ∧ p1) ∨ (p5 ∧ False))) → p4)) ∨ (p4 → ((p1 ∧ p4) → p4)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68269808749830104223239999120 : ((p3 → ((p4 ∧ (p1 ∨ (((((False ∨ (p1 ∧ (p2 ∧ p2))) ∨ p2) ∧ (p1 → p4)) ∨ (p2 ∨ p4)) ∧ (p4 ∧ p3)))) ∨ (p4 → p3))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136300151964143083077269094998 : (((p3 → (True ∨ ((False → p4) → p1))) → ((p5 ∨ p5) → (((p5 ∨ (p5 ∨ ((p3 ∧ p3) ∨ p4))) → p1) ∧ p2))) ∨ (False → (p5 ∧ p3))) := by
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
theorem thm_5_vars_327789887934592814259867597693 : (True → ((((((((p3 → p5) → (False ∧ ((p5 ∨ True) → (False → True)))) → (p4 ∨ (True ∧ False))) ∨ p4) ∨ p4) → p4) ∧ p3) ∨ (p2 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53162083194443959321116023087 : ((((False ∨ (((p4 ∨ (False ∧ True)) ∨ (p3 ∧ p5)) ∧ True)) ∨ p2) ∨ ((((p3 ∨ (p4 → p5)) ∨ p5) ∨ p2) ∨ ((False → True) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57190865277734864309048826591 : ((((p2 ∨ p3) ∨ p5) ∨ (((p1 ∧ ((p2 ∧ False) ∨ ((p4 ∧ p5) ∨ p2))) ∨ ((((p4 → False) ∨ p2) ∧ p3) ∧ p2)) → (p4 ∨ True))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629984195115598728464995159602 : ((((((((p2 → p1) ∧ True) ∨ p4) ∨ (True ∧ ((((p2 ∨ (p3 ∧ (p5 ∧ (p1 → p1)))) ∧ False) ∧ (p2 ∧ True)) ∧ p1))) ∨ p4) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55197285831747931874802287060 : ((((False → (True ∧ (p4 ∨ p5))) → False) ∨ ((False ∧ (p3 ∧ False)) → (False ∧ ((p3 ∨ p5) → (((p5 → p5) → (p5 ∨ p3)) ∧ p1))))) ∨ p5) := by
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
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- False on the left can always be used.
    apply False.elim h10
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- False on the left can always be used.
    apply False.elim h13
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h1.left
    let h17 := h1.right
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38959903533278403075415883112 : ((((p2 → (False ∨ p3)) → ((((p4 → ((((p5 ∨ p5) ∧ p5) ∨ p3) ∨ p3)) ∧ p5) → (False ∨ (p4 ∨ p1))) → (p5 ∧ p1))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58011072831063968774834629954 : (((True ∧ False) ∧ (p1 → ((((p2 ∧ (p3 → p1)) ∨ ((((p3 → (True ∨ (p2 ∨ (p1 → p4)))) ∨ p4) ∧ False) ∨ p2)) ∨ p3) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161515434496524964431119107135 : ((p4 ∧ (p1 ∧ ((p4 ∧ (((p1 ∨ ((p4 → (p5 → p2)) → p1)) ∨ (False ∨ False)) → p3)) ∧ p3))) → ((((p3 → p2) ∧ p5) ∨ p3) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38551281527446301785070650891 : ((((p1 ∨ (p2 → ((p4 ∨ ((p5 ∨ False) ∧ p3)) ∧ p3))) ∧ (((p1 ∨ (True ∨ ((True → True) → p5))) ∧ (True ∨ p1)) ∨ p1)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311112503084932003581237880944 : (p2 ∨ ((p2 → p3) ∨ ((((p4 ∨ p2) ∧ (p5 → True)) ∨ (((p4 ∨ ((p1 ∨ p1) ∨ p5)) ∨ (False ∨ ((p4 → True) ∨ p5))) ∨ False)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330451262724863338149177080652 : (True → (p3 ∨ ((p5 ∧ p4) ∨ ((True ∨ p2) → ((((p4 ∧ False) → p4) ∨ p2) ∧ (p5 → (((True ∧ p4) ∨ p4) ∨ (False → (False ∨ True))))))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320983230437705770230435572195 : (p4 ∨ (False ∨ (((p5 ∧ ((False → p3) → (((p2 ∨ (True → ((p2 ∨ p4) ∧ (((p1 → p1) ∧ True) ∧ False)))) ∨ p4) ∧ False))) → p2) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (False → p3) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186941780287274241210137465610 : (((p4 → (p2 ∧ p3)) ∧ (((p4 → p1) ∧ (p4 ∨ False)) ∧ p2)) → ((((True ∨ p4) → False) ∧ ((True ∨ (p2 → p3)) ∨ (p1 ∧ True))) ∨ True)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180709417251594627937757471925 : ((((p4 → (True ∨ p2)) → False) ∧ (((p5 → True) ∨ (p3 → p3)) ∨ p2)) → (((p3 ∧ ((p2 ∧ p2) ∨ False)) ∧ p4) ∧ ((True → False) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : (p4 → (True ∨ p2)) := by
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h6
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : (p4 → (True ∨ p2)) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h10
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : (p4 → (True ∨ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h15
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h16 := h2 h14
    -- False on the left can always be used.
    apply False.elim h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h21 : (p4 → (True ∨ p2)) := by
        -- Implications on the right can always be decomposed.
        intro h22
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h23 := h17 h21
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h25 : (p4 → (True ∨ p2)) := by
        -- Implications on the right can always be decomposed.
        intro h26
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h27 := h17 h25
      -- False on the left can always be used.
      apply False.elim h27
  case inr h28 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h28
    -- One of the premise coincides with the conclusion.
    exact h28
  -- Conjunctions on the left can always be decomposed.
  let h29 := h1.left
  let h30 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h30
  case inl h31 =>
    -- Disjunctions on the left can always be decomposed.
    cases h31
    case inl h32 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h33 : (p4 → (True ∨ p2)) := by
        -- Implications on the right can always be decomposed.
        intro h34
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h35 := h29 h33
      -- False on the left can always be used.
      apply False.elim h35
    case inr h36 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h37 : (p4 → (True ∨ p2)) := by
        -- Implications on the right can always be decomposed.
        intro h38
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h39 := h29 h37
      -- False on the left can always be used.
      apply False.elim h39
  case inr h40 =>
    -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
    have h41 : (p4 → (True ∨ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h42
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h29, we can now drive its conclusion.
    let h43 := h29 h41
    -- False on the left can always be used.
    apply False.elim h43
  -- Conjunctions on the left can always be decomposed.
  let h44 := h1.left
  let h45 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h45
  case inl h46 =>
    -- Disjunctions on the left can always be decomposed.
    cases h46
    case inl h47 =>
      -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
      have h48 : (p4 → (True ∨ p2)) := by
        -- Implications on the right can always be decomposed.
        intro h49
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h44, we can now drive its conclusion.
      let h50 := h44 h48
      -- False on the left can always be used.
      apply False.elim h50
    case inr h51 =>
      -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
      have h52 : (p4 → (True ∨ p2)) := by
        -- Implications on the right can always be decomposed.
        intro h53
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h44, we can now drive its conclusion.
      let h54 := h44 h52
      -- False on the left can always be used.
      apply False.elim h54
  case inr h55 =>
    -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
    have h56 : (p4 → (True ∨ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h57
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h44, we can now drive its conclusion.
    let h58 := h44 h56
    -- False on the left can always be used.
    apply False.elim h58



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193454255630044111749421490353 : (((p5 → False) ∧ ((p4 → (False → p5)) → (p2 ∨ False))) → (((((p5 → p4) → False) ∧ p2) ∨ True) ∧ ((((p2 → p4) ∨ True) ∨ p4) ∧ True))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172792172775105551484519092881 : (((p1 → p5) → ((p1 ∨ (p5 ∧ ((p5 ∧ p5) → ((False ∨ p1) ∨ p5)))) → p3)) ∨ (p1 → ((False → ((p3 → p4) ∨ p1)) ∨ (False ∨ False)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950162627454640290378787613675 : (((((p4 ∨ True) → False) ∧ (((((p4 ∧ ((False ∧ p4) ∨ p1)) ∨ p5) → (True ∨ (False ∨ (False → (p1 ∧ p2))))) ∧ (p5 ∨ p4)) ∨ True)) → p3) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : (p4 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : (p4 ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : (p4 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- False on the left can always be used.
    apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53832400110682794028284268615 : ((((p2 → ((True ∧ (p1 → p2)) ∨ False)) → (p2 ∧ False)) ∨ (((p5 ∧ p3) ∧ p1) ∨ (((p1 ∨ p3) ∧ (p3 ∧ (p5 ∧ p1))) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218593716320919204955073634754 : (((p3 → p1) → (p1 → p3)) → (p2 ∨ ((p2 ∨ False) ∨ (p5 → (((p2 ∧ ((p2 ∧ (p4 ∨ (True ∨ p1))) ∧ p3)) ∧ p1) ∨ (p4 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_301079863923815488755940841560 : (False ∨ ((((True → False) → (p5 → (p3 → (p4 ∧ False)))) → p3) → (p5 ∨ (p3 ∧ (False → (((p3 ∧ p2) → p1) ∨ ((p5 ∧ p5) → p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True → False) → (p5 → (p3 → (p4 ∧ False)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- False on the left can always be used.
    apply False.elim h7
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305812429075301340595907484453 : (p1 ∨ ((p1 ∧ (p3 ∧ (True ∨ (p1 → (True ∧ p5))))) → (((p2 → False) → (p3 → ((p4 ∨ ((True → p2) ∨ p3)) → (True ∧ False)))) ∨ p3))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157640335878895262961820828864 : (((False ∨ (p2 ∧ (((p4 ∨ True) ∧ ((True ∨ p5) ∨ (p5 ∨ p4))) ∧ p2))) ∧ ((p1 ∨ False) ∧ p3)) ∨ ((False ∨ (True ∨ p4)) ∨ (p3 ∨ False))) := by
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
theorem thm_5_vars_657292109888953825686614372165 : (((((p2 ∧ True) ∧ (((((p4 ∧ (p1 ∨ (p3 → p4))) → p1) ∧ (p3 ∧ True)) → (((p1 → p4) → p2) ∧ p1)) ∨ p3)) ∨ (True ∨ p1)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_111878243921552559356146951167 : ((((((p3 → (p2 ∧ p1)) ∧ (p2 ∨ ((p2 ∧ p5) → True))) ∧ ((True ∧ False) → False)) → ((False ∨ p3) → (p2 ∨ p1))) ∨ True) ∨ (p2 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115793134742899808480763744509 : (((((p2 ∧ p1) → p1) ∨ p2) ∧ (p1 ∨ (((p4 → p2) → p3) → ((p5 ∨ (p4 ∨ p4)) ∨ ((False ∧ (p4 → p4)) ∨ p5))))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193825141062871538614651719784 : ((p5 ∧ (True ∧ (((p3 ∨ p5) ∧ True) ∧ (True → True)))) → ((False ∨ p3) ∨ ((p3 ∧ (p4 ∧ p3)) ∨ ((p3 → ((p1 → p3) ∧ p3)) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h13
    -- One of the premise coincides with the conclusion.
    exact h12
    -- One of the premise coincides with the conclusion.
    exact h12
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149141707485584497705932831055 : (((p5 ∧ p5) ∧ ((((p1 → ((False ∨ p4) → (p3 ∨ (p1 ∨ (False → False))))) ∧ True) → (p2 ∧ p2)) ∨ p1)) ∨ ((p1 ∨ True) ∨ (p2 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324085482816042903907317018128 : (p5 ∨ (((p3 → (True ∧ False)) → (((p4 → (p5 ∧ False)) → False) → p2)) ∨ ((False ∨ ((p5 ∧ p3) ∨ (((p5 ∨ p2) ∧ False) → p4))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299221684943000813754926644752 : (False ∨ (((((p2 ∧ ((p2 ∧ (True ∨ (p3 ∧ False))) ∨ (p5 ∨ (p1 → True)))) ∧ (p2 ∧ ((p4 ∨ False) ∧ True))) ∧ p2) → (p1 → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650257686517699483742993700877 : ((((((((p2 ∨ p1) ∨ p5) → ((((True ∨ p1) ∨ (False ∧ False)) → p3) ∨ p4)) → p5) → (p3 → ((p3 ∧ p2) ∧ p3))) ∧ (False ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141313485244823949073196715426 : (((p3 → (p5 → (p1 → p2))) ∧ ((((((p3 ∧ p1) ∨ p1) ∨ False) → ((p4 ∨ p5) → p3)) ∨ True) → (False ∧ p5))) → (True ∧ (p5 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (((((p3 ∧ p1) ∨ p1) ∨ False) → ((p4 ∨ p5) → p3)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318632308130265646898923799385 : (p4 ∨ ((p2 ∧ (((p5 ∧ p3) ∨ p4) ∨ ((((p4 → p4) ∨ ((p2 ∧ p2) ∨ p1)) ∨ p1) ∨ ((p3 ∨ p1) ∧ (p5 ∨ p2))))) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158746089112821005294074577406 : ((p4 ∧ ((((p3 ∧ p3) → ((p5 ∨ p4) → False)) → ((p1 ∨ p1) ∧ ((p1 ∧ p4) → p4))) ∨ p4)) ∨ ((True → p5) → (p1 → (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304313976900486427103297816565 : (p1 ∨ ((((((p2 ∨ True) → (((True → True) ∧ True) ∨ p2)) ∨ p4) → (False ∨ (p5 ∨ p1))) ∧ ((p2 ∨ (p5 ∨ (p1 ∨ False))) → False)) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p2 ∨ True) → (((True → True) ∧ True) ∨ p2)) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h4
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h14 : (p2 ∨ (p5 ∨ (p1 ∨ False))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h15 := h3 h14
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76689011970458735133961220551 : ((((p5 ∨ (p5 ∧ (p2 ∨ (((p2 ∧ False) ∧ ((True → p5) ∧ (False ∧ p1))) ∧ False)))) ∨ ((True → (p2 ∨ p3)) ∨ (True → True))) → p4) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∨ (p5 ∧ (p2 ∨ (((p2 ∧ False) ∧ ((True → p5) ∧ (False ∧ p1))) ∧ False)))) ∨ ((True → (p2 ∨ p3)) ∨ (True → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147210549741814069909322698193 : (((p2 → ((((((p1 → (p3 → p1)) ∨ ((p2 → p5) ∧ p4)) → False) ∧ (p3 ∨ p1)) ∧ True) ∨ p1)) ∧ p4) ∨ (p1 ∨ (p5 ∨ (True ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248698355588058222930340976445 : ((p3 ∨ p2) ∨ (((((p5 ∧ (p4 → p1)) ∨ (p5 ∨ (p3 ∧ p4))) ∨ (p5 → p4)) → (p1 → (False ∨ (True → p4)))) ∨ (True → (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328092018193039818588505663278 : (True → (((((((((p3 ∨ p1) → (True ∧ p1)) ∨ p1) ∨ True) ∧ p3) ∨ ((p1 ∧ p1) ∧ p5)) ∨ (False → p4)) ∧ True) ∨ (p5 ∧ (p5 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_146998791891474537083090033050 : ((((((p2 → (p3 → (p4 ∧ p1))) → p2) ∨ (p4 → (p2 ∧ ((p1 → False) → p2)))) ∧ (p2 → p1)) ∧ False) ∨ (p3 ∨ (False ∨ (False → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677625236021098158102595868645 : ((((((((p4 ∧ (((p3 ∨ p5) ∧ ((True → p1) ∨ (p1 ∧ p1))) → p2)) → p5) ∨ p1) → True) → p3) ∨ (False ∨ ((True ∨ p3) ∨ p4))) ∨ p5) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38394025073892914804909074705 : ((((((p3 ∧ p5) → p4) → ((False ∨ (True ∨ ((False → False) ∧ False))) ∨ (p2 → p1))) → (p4 → ((p1 ∨ p1) → (True ∧ p2)))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40189772734712683666463761974 : (((((p4 → (p3 ∧ False)) ∧ (((((p1 ∧ p3) ∧ (False ∧ p3)) ∨ ((p3 → p3) ∨ ((p3 → p1) → p3))) ∨ p5) ∧ p4)) ∧ p1) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254435051039613651831405105967 : ((p2 ∧ p5) → (False ∨ (p3 ∨ (((((p4 ∧ p5) → p2) → ((p5 ∨ p4) ∨ False)) → (((((p1 ∨ p4) ∧ p3) → p1) → p4) → p4)) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149131001109044826361383031483 : (((p3 ∧ p2) ∧ ((p4 → (p3 ∧ (False ∧ (((p5 → (True ∨ p2)) → p3) → ((p2 → p1) ∧ p1))))) → p2)) ∨ ((p1 ∧ False) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41371209804818577482552282621 : (((((p3 ∨ p1) ∨ ((p1 ∨ ((p2 ∨ (True ∨ (True ∧ p2))) → p5)) → (p5 ∧ False))) → (p3 ∧ (p1 ∨ (p2 ∨ (p5 ∧ p2))))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686367905305670971517722392084 : ((((((p4 ∧ (p4 → False)) ∧ p5) ∧ (((((True ∨ (p3 → p4)) ∨ p2) → p2) ∨ p4) ∨ p1)) → ((((p3 ∨ p2) ∨ False) ∧ p1) ∨ p4)) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637954852925538609599539981048 : (((((p4 → (p5 ∨ (p3 → (False ∨ (p2 → True))))) ∧ (((((p3 ∨ (False ∨ p5)) → (p4 ∧ (p2 → True))) ∨ p1) → False) ∧ p3)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69140536229942247796650774836 : ((p5 → ((((p3 → p1) → (p4 ∧ (p3 ∧ ((p5 ∨ p3) ∨ ((False ∧ p2) ∨ (p2 ∨ (p4 ∧ p1))))))) ∨ p5) ∨ ((p5 ∧ p2) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171613607089134068943874009797 : ((((p4 ∨ ((p3 ∧ p5) ∨ p2)) ∨ ((((p2 ∧ p1) → True) → p5) → False)) ∨ True) ∨ (((True → True) → ((False → (False → p5)) ∧ p1)) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234163251917846740951471150785 : ((True → (p2 → p4)) → ((p1 ∧ ((p5 → p3) ∨ (((p3 → p4) ∨ False) → p5))) ∨ (p3 ∨ (False → (False → ((True ∧ (p4 ∨ p1)) ∧ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642085807672020018974451158388 : ((((True ∧ (((True ∧ (p3 ∧ True)) → ((p4 ∧ (p2 → (p1 ∨ (p2 ∧ (((True → True) ∨ True) ∧ p2))))) ∨ p1)) → (p1 ∨ p5))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56391344557649463799723762694 : (((((True → p4) → p4) → p5) → (p5 → (((((((True ∧ p2) ∧ p4) ∨ (p3 ∧ True)) ∧ True) ∨ p4) ∨ (p5 ∨ p1)) ∨ (p1 ∧ p3)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1556734014944899813832370071 : ((p2 ∨ ((p5 ∧ False) ∧ (p4 ∧ (True ∧ (p3 ∧ ((True → (p4 → (p5 ∧ (p4 ∨ (p4 ∨ p4))))) → (p3 ∧ True))))))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38569137510640530499117260072 : ((((True ∧ (((p2 → (p3 ∧ True)) ∨ (p5 → p5)) ∧ p1)) ∨ ((((p5 → p2) ∧ p4) ∧ ((p2 ∧ p1) → p5)) ∧ (True ∧ p2))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52461660367582461234559785984 : (((False ∨ (((p2 ∧ (p2 ∧ (p4 ∧ p5))) ∨ True) ∨ (p2 ∧ (p3 ∧ p3)))) ∧ ((p4 ∨ (p2 ∧ p4)) → (p4 ∨ (p3 ∨ (p5 → p4))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306238990696184084579734100966 : (p1 ∨ (((p5 → True) → p4) → (((p2 ∧ (((p3 → (False → (True ∧ p1))) → p1) ∨ p2)) ∧ (True ∨ True)) → (p5 → ((p1 ∨ False) ∨ p5))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138530331121517553341414534222 : ((((((p3 ∧ (p2 → p4)) ∧ (((p2 ∨ (p5 → p4)) ∨ True) ∧ (p3 ∨ p5))) ∨ ((p3 ∧ False) → p2)) ∨ p4) ∧ True) → ((p1 ∧ p4) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h7.left
      let h11 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
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
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h23 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64031354734717215696987179876 : ((False ∨ ((p1 → ((p2 ∨ p4) ∧ ((p1 ∨ p1) ∨ ((False ∨ (p2 ∨ p4)) ∧ (False ∨ (((p2 → False) ∧ p5) ∨ True)))))) → (p5 ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746021034480303046928661490313 : ((((p1 ∨ True) → (((((((False ∨ (p4 ∧ ((p5 → p2) ∧ True))) → (False ∨ (p2 ∨ (p2 → p5)))) → p4) ∨ p1) ∧ p1) ∨ p3) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83351713238277933452955083518 : ((((p3 ∨ False) ∧ ((((p3 → p1) ∧ True) ∧ (p5 ∧ (False ∨ (p3 → p4)))) ∧ (p2 → p5))) ∧ (p3 ∧ (p4 → (p2 ∧ (p4 → False))))) → False) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h10.left
    let h14 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h3.left
      let h18 := h3.right
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h19 : p4 := by
        -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
        have h20 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h17
        -- We have shown the premise of h16, we can now drive its conclusion.
        let h21 := h16 h20
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h22 := h18 h19
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h24 : p4 := by
        -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
        have h25 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h17
        -- We have shown the premise of h16, we can now drive its conclusion.
        let h26 := h16 h25
        -- One of the premise coincides with the conclusion.
        exact h26
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h27 := h23 h24
      -- False on the left can always be used.
      apply False.elim h27
  case inr h28 =>
    -- False on the left can always be used.
    apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56578029812114010547560858358 : (((False → (p4 ∧ (p4 ∧ p5))) → (p3 ∨ ((True ∨ ((((False ∨ p1) → p5) → p5) ∧ False)) → (p2 → (p2 ∧ (p3 ∨ (p4 ∨ p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190869067219304698850042427534 : ((((p1 → (p5 → True)) ∧ (False → p3)) → (p5 → p2)) ∨ (p1 → (p1 → (((((p4 ∧ p4) ∧ (True ∨ False)) ∨ p2) ∨ True) ∨ (p2 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703674971519178552053550213012 : ((((((((p2 ∨ (p5 → False)) ∧ False) ∧ p3) → True) ∧ p1) → (((p1 → p4) ∨ p5) → (((p4 ∧ (False → p3)) ∧ (True ∧ p1)) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227752757666323267567492263560 : ((p1 ∧ (p3 ∨ p4)) ∨ ((p2 ∨ (p4 ∨ ((((p3 → (True ∨ True)) ∨ (p4 → True)) ∨ p1) ∨ ((p4 ∧ p4) ∧ (p3 ∨ p2))))) ∨ (False ∨ p4))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115863350086647042640386059232 : (((p2 → ((p2 → True) → p4)) ∧ (((((p4 ∧ False) ∧ p4) ∨ p2) ∨ True) ∧ ((p3 ∨ (False ∧ ((False ∨ p4) ∧ True))) ∨ True))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_989579044485722433473563620480 : (((p3 ∧ ((True → (False ∧ p3)) ∧ ((((((False ∧ True) → (p3 ∧ p3)) ∧ ((p5 ∧ True) → (p5 → (p4 ∨ False)))) ∧ p4) ∧ p5) ∨ p3))) → False) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h14 := h4 h13
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h18 := h4 h17
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- False on the left can always be used.
    apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264749805120634265637403099714 : (True ∧ ((False → True) ∧ (((False ∨ ((p1 ∨ p1) ∨ True)) → ((p1 → (p2 ∨ (p3 ∧ p1))) ∧ p1)) ∨ (False → ((True ∧ True) → (True → False)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342890203506155079102788549213 : (p2 → ((((p1 ∧ (p3 ∧ p1)) ∧ False) → p1) → ((((p2 ∨ p4) → (p1 ∧ ((p3 → False) ∧ (((True → True) → p1) ∧ False)))) ∨ True) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160097696007222731994212832028 : (((p5 ∨ (False ∨ (p1 ∧ (False ∧ (True ∧ (p2 ∧ (False ∨ (p1 ∧ (p3 ∨ (True ∨ p1)))))))))) → p4) → (p4 → ((p1 ∧ p5) ∨ (p2 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42891146533743839107787748658 : (((p3 → ((p1 ∧ ((p5 → p4) → (((True ∧ (((False → p2) → False) ∨ p4)) ∨ ((p2 ∧ p5) → p1)) → p4))) ∧ (p1 → p3))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307890433043242607100491024346 : (p1 ∨ (p5 → (p5 ∧ (((((p2 → (p1 ∨ False)) ∧ (p3 ∧ True)) ∨ p3) ∨ (True ∨ p5)) ∨ (((p5 ∨ p3) ∨ True) → ((p5 ∨ p5) ∧ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780191876128394204505204883765 : (((p2 ∨ (((((p2 ∨ (False ∧ (((True ∨ (p1 → p2)) ∧ p4) ∨ p3))) ∨ ((p4 ∨ p3) ∧ p3)) → p3) → p1) ∨ (p5 → (True ∨ False)))) ∨ False) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319043431876180746015783054576 : (p4 ∨ (((p4 ∨ ((p4 ∧ (p4 ∧ False)) ∨ (p4 ∨ (p5 ∧ (p5 ∧ p1))))) ∨ (p3 ∧ ((p5 ∨ p2) → p3))) ∨ (p5 ∨ (p4 → (p4 ∨ p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147533225052350296490149692642 : (((p1 → ((((p2 → ((False → p1) ∧ (p2 ∧ (p3 → (p1 → (p4 ∧ False)))))) ∨ p1) → p2) ∨ p1)) ∨ p2) ∨ ((True ∧ (p1 ∨ p1)) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180565733082986009208216975265 : (((((False ∨ ((False → p4) ∨ p5)) ∨ False) → False) → ((p2 ∨ True) ∨ p5)) → ((p4 ∨ (p4 ∨ (False → ((p1 ∨ p4) ∧ (p5 → True))))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118811373070738123936476793541 : ((True → (((((p1 → ((False ∨ True) ∧ p3)) ∧ ((True ∨ True) → p4)) ∨ ((p5 ∨ (True → False)) ∧ False)) → (p3 → False)) ∨ p5)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41926802978385682748923507400 : ((((False ∨ (p3 → p2)) → ((p5 ∨ (p1 ∧ p4)) ∧ ((((False ∧ (p1 ∨ p2)) → p3) → (p4 ∧ True)) ∨ (p3 ∨ (p5 ∨ False))))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323235270746306409052606147004 : (p5 ∨ ((((p4 → p5) ∧ p1) ∧ (((p1 ∧ ((p4 ∧ p3) ∨ p2)) → (((True ∨ (True ∨ p5)) ∧ True) → p1)) → (p2 → False))) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177678079287027043234964986749 : (((((True → (p5 → p1)) ∨ (p5 → (p4 → (p3 → p1)))) → False) ∧ True) ∨ ((p4 → False) ∨ ((False ∨ p2) ∨ (False → (p5 ∧ (False ∨ True)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173129791744935253603878725197 : ((p2 ∨ (p1 ∨ (p3 → (p1 ∨ (p4 ∨ (p2 ∧ ((p1 → (False ∧ p2)) ∧ p5))))))) ∨ (((False ∧ p4) ∧ (p2 → ((p3 → True) → True))) → p2)) := by
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53954344130058953408885644179 : ((((((p4 ∨ ((False ∨ False) ∨ p5)) ∨ p4) ∧ p1) ∧ p1) → (p4 ∨ ((p1 → (False ∨ (((p3 ∨ p3) ∨ p3) ∨ (p1 ∧ True)))) ∨ False))) ∨ p4) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- False on the left can always be used.
          apply False.elim h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h13
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h13
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_893953807592507753444381765926 : (((((p4 ∨ p4) → (((p3 ∧ ((((((p1 → False) ∧ p4) ∨ p5) ∧ p5) ∨ p1) ∧ (p2 ∨ p1))) → p1) ∧ False)) ∧ (p4 ∧ (p2 ∧ p4))) → False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : (p4 ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328098561542891727787085732535 : (True → (((((p4 ∨ (False → ((p1 → (False ∧ (p5 ∧ p1))) ∨ p3))) → (True → p1)) ∧ (p2 ∨ (p5 → p3))) ∨ False) ∨ ((False → False) ∨ p3))) := by
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
theorem thm_5_vars_313046999461069368107624168626 : (p3 ∨ (((((((True ∧ (p2 → (False → (p1 ∨ False)))) ∨ p3) → p1) ∧ (p1 ∧ True)) → ((((p4 → p3) ∧ False) ∧ p3) ∧ p2)) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201781917821737113452297881791 : (((((p2 → p1) ∨ p3) → p3) ∨ True) ∧ ((p5 ∨ (p4 ∧ (p5 ∧ p3))) ∨ (p4 ∨ (p5 ∨ (False → ((p1 → p1) ∧ ((p2 ∨ False) ∨ True))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607827002064053680156625047531 : (((((p4 ∨ ((True ∨ ((p2 ∨ p2) ∧ p1)) ∧ ((True ∧ p1) → (p4 ∨ (((p1 → p2) → ((p5 → p2) ∧ p2)) → p3))))) ∧ p3) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225415932248695070323598933755 : (((p3 ∨ p1) ∧ False) ∨ (((((True → (((((p3 ∧ (p1 → p3)) ∨ p3) ∧ True) ∨ True) → (p2 ∨ p4))) ∨ p4) → p4) ∧ p2) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141183622404929107215685675602 : (((((p3 → (False ∨ p3)) ∧ True) → p5) ∨ (((p3 → p3) ∧ p2) ∧ (((p1 ∧ True) → p1) ∨ ((p3 → False) ∧ p2)))) → (p5 ∨ (True ∨ False))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64786514852089982344389464235 : ((p2 ∨ ((((False ∨ ((((p5 ∨ False) ∧ p3) ∨ True) ∨ (True → p5))) ∧ (p5 ∨ (p5 → True))) ∧ ((p1 ∧ (p4 ∧ p3)) ∨ p5)) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42287435413533053702063684562 : (((p1 ∧ (p3 → ((p2 ∨ (False ∨ (((p5 ∧ p4) ∨ False) ∧ (((True → (p2 → p1)) → (p5 → True)) ∨ (p5 ∧ False))))) ∨ p2))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962429227476543306226960621513 : ((((True → False) ∧ (p3 → (p4 ∨ (p5 ∨ ((p2 → ((((False ∧ p3) ∨ (p2 → p5)) ∧ True) → p5)) → (True ∨ (p5 → (p4 ∧ p2)))))))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186395380029825265691573361089 : (((p4 ∧ ((False ∧ (p5 ∨ (p5 → (p2 → p3)))) ∨ True)) → True) → ((p2 ∧ (True ∧ ((p3 ∨ (p3 → False)) → (p4 → p3)))) ∨ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68965076695358970735293933983 : ((p4 → (p2 → (p3 → (((p4 → ((False ∨ p3) ∨ p4)) ∨ (False → (True → (p2 ∧ (True ∧ (p3 ∨ (p4 ∧ p5))))))) → (p5 ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685919503141539746273586494802 : (((((((p1 ∨ False) ∨ (((False → (False → p4)) ∧ p5) ∧ (p3 → p5))) ∧ True) ∧ (p3 ∨ p4)) → (p4 → (p3 → ((True → p2) ∨ True)))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h10 =>
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
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327030004138448465055464700283 : (True → (((((False → (p1 ∨ ((True → p4) ∨ p1))) → p5) ∨ (p2 ∧ p3)) → ((True ∨ ((True ∨ (p3 → (p5 ∨ p3))) → p2)) → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



