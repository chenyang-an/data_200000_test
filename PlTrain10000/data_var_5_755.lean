variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245405594704858993102393492125 : ((p2 ∧ p4) ∨ (((p5 → p4) ∨ ((((p3 ∨ (p2 ∧ p3)) ∧ ((False → (p1 → ((p4 ∧ False) ∨ (p3 ∧ p1)))) ∧ p4)) → p1) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2459841531497262250342540619 : ((((p2 ∧ (p3 → False)) ∨ p5) ∧ ((p2 → p1) → p2)) ∨ (p5 → ((((True ∧ ((True → (True → p2)) ∨ False)) ∧ p2) ∨ p3) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764883906508695707601184860081 : (((p4 ∧ ((((((False → True) ∧ p2) → (p2 ∨ ((False ∨ p2) ∧ p3))) → True) ∨ (p3 ∨ (p3 → (p4 → ((True ∧ False) → p5))))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41611356036136304479584774115 : ((((p3 ∧ (p3 ∧ ((p5 ∧ False) ∨ (p2 ∧ False)))) ∨ (False → ((p1 ∧ p2) ∧ (p2 ∧ (True ∨ (p2 ∨ ((p1 ∨ p5) → p1))))))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589221714636533005005470074856 : ((((((((p2 → p3) ∨ (False ∧ ((True → p4) ∧ (p2 ∧ ((False ∨ p4) ∧ True))))) → (((p5 ∧ p1) ∧ False) → True)) ∧ p2) → p5) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763816058467709324242357327016 : (((p3 ∧ (p3 ∨ ((((True ∨ (((False → (p1 ∧ p2)) ∨ p3) ∨ ((p3 ∨ p1) ∨ p5))) ∨ (p3 ∧ ((p4 ∨ False) ∨ p1))) ∧ p5) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192117348143115310799767522250 : ((p5 → (((p1 ∨ p3) ∧ (p5 ∧ (p3 ∧ p1))) ∧ p4)) ∨ ((((p5 ∧ p5) ∧ (p1 ∧ (p3 ∧ p2))) ∨ ((True → (False ∧ p1)) ∨ False)) → p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h4.left
    let h8 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h14 := h12 h13
      -- We need to get the left conjuct of h14 based on <expert-advice>.
      let h15 := h14.left
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168056145282131226382374304496 : (((((p3 ∨ p1) ∨ p4) ∧ p3) ∧ (True → ((((p4 ∧ True) ∧ p2) ∨ (True ∧ p4)) ∧ False))) → ((p2 → False) ∧ ((p3 ∧ (True ∨ True)) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h10 := h4 h9
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h14 := h4 h13
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h18 := h4 h17
    -- We need to get the right conjuct of h18 based on <expert-advice>.
    let h19 := h18.right
    -- False on the left can always be used.
    apply False.elim h19
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h20.left
  let h23 := h20.right
  -- Disjunctions on the left can always be decomposed.
  cases h22
  case inl h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h26 =>
      -- One of the premise coincides with the conclusion.
      exact h23
  case inr h27 =>
    -- One of the premise coincides with the conclusion.
    exact h23
  -- Conjunctions on the left can always be decomposed.
  let h28 := h1.left
  let h29 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h30 := h28.left
  let h31 := h28.right
  -- Disjunctions on the left can always be decomposed.
  cases h30
  case inl h32 =>
    -- Disjunctions on the left can always be decomposed.
    cases h32
    case inl h33 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h34 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h35 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h36 := h1.left
  let h37 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h38 := h36.left
  let h39 := h36.right
  -- Disjunctions on the left can always be decomposed.
  cases h38
  case inl h40 =>
    -- Disjunctions on the left can always be decomposed.
    cases h40
    case inl h41 =>
      -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
      have h42 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h37, we can now drive its conclusion.
      let h43 := h37 h42
      -- We need to get the right conjuct of h43 based on <expert-advice>.
      let h44 := h43.right
      -- False on the left can always be used.
      apply False.elim h44
    case inr h45 =>
      -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
      have h46 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h37, we can now drive its conclusion.
      let h47 := h37 h46
      -- We need to get the right conjuct of h47 based on <expert-advice>.
      let h48 := h47.right
      -- False on the left can always be used.
      apply False.elim h48
  case inr h49 =>
    -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
    have h50 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h37, we can now drive its conclusion.
    let h51 := h37 h50
    -- We need to get the right conjuct of h51 based on <expert-advice>.
    let h52 := h51.right
    -- False on the left can always be used.
    apply False.elim h52



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223994593214305134852971880988 : ((p4 ∨ (False → p1)) ∧ (p1 → ((p5 ∧ ((((False ∨ ((False → p2) ∧ ((False ∨ p4) ∨ p1))) → p4) → p4) ∧ (False ∨ p2))) ∨ (True ∧ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57738838642772654478982065586 : ((((p4 ∨ p5) → True) → (((((p2 ∨ ((True ∨ (False ∧ False)) ∧ (p2 → (p2 ∧ (p3 ∨ (p1 ∧ p4)))))) → p4) → False) ∨ True) ∨ p4)) ∨ p5) := by
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
theorem thm_5_vars_116048659106487369199852791687 : (((p1 → (p2 ∧ (p3 ∨ p4))) → ((((p2 → (p1 → p3)) ∧ ((p2 ∨ (False → (p5 → True))) → p1)) ∧ (p3 ∧ p3)) ∨ True)) ∨ (p4 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172529431997727823430358319231 : (((p3 ∨ (p2 → False)) ∧ ((p3 ∨ p5) ∨ ((True ∨ (p3 ∧ p3)) → (p1 → p5)))) ∨ (((True ∨ p2) ∨ p4) ∧ (p4 ∨ ((p2 ∨ True) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593482031020059541235456286538 : (((((((p2 → p5) → p1) ∧ (p4 → (((p3 → (p1 → (p3 ∨ p3))) ∨ (p2 ∧ (p3 → p4))) ∧ p2))) → ((False → p5) → False)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40393997543521679642004665719 : ((((((p3 ∨ p4) → (p1 → ((p2 ∨ (p4 ∧ (False → ((p5 ∨ (p4 ∧ p4)) → p1)))) ∨ (p2 ∨ p5)))) → (p4 → False)) ∨ p4) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197721411376559910889674258283 : ((((p3 → p5) ∧ p4) ∧ (False ∧ (p3 ∨ p2))) ∨ (False ∨ ((True → True) ∨ ((p1 ∧ ((p5 → (p3 ∧ ((p5 → False) ∨ p3))) → p4)) ∧ p5)))) := by
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
theorem thm_5_vars_64977840938117713512825322195 : ((p2 ∨ (((True ∨ (p3 ∨ p3)) ∧ p5) ∨ ((((p2 ∧ p1) ∨ (p3 ∨ p5)) ∨ True) ∨ (((p3 → p1) ∧ p1) ∨ ((p3 ∧ p5) ∨ False))))) ∨ False) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230074287694944092942027642645 : (((p2 ∧ p3) ∧ p3) → (((False ∧ ((((p2 ∧ (p2 → (p3 → ((p5 ∧ True) ∨ (p3 ∨ p4))))) → p1) → False) ∧ p4)) ∨ p3) ∨ (True ∨ p5))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612796058147285094402348457135 : ((((((False → p3) ∧ (((True → (p3 ∨ (((((p4 ∨ p3) ∨ p2) → p5) ∨ (False ∨ p1)) → p5))) → False) ∨ True)) ∨ (True ∧ False)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_711245899815104050751358121369 : ((((p4 ∧ (p5 → (p1 → (True ∨ True)))) ∧ ((p5 ∧ (((p1 ∨ False) → (False ∧ (p1 ∧ (p4 → (False → (p3 ∧ p1)))))) ∧ p2)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669734169399126284665817255000 : (((((False ∨ (False → ((((p4 → p3) ∧ True) → ((p5 ∨ p4) ∨ p4)) → p5))) ∧ ((True ∨ True) ∧ (p1 ∧ p1))) ∨ ((p2 → p1) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46163224261595588940361378642 : (((((p2 → (p3 ∧ (((p4 ∨ p4) → (p4 → True)) ∨ (True ∧ True)))) ∨ (((True ∧ (p4 ∨ p1)) ∨ p1) → p1)) → p5) ∧ (p2 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340797418594337621915318525786 : (p2 → (((p2 ∧ ((((True ∨ (False → (p2 → p2))) ∧ p2) ∧ ((p3 ∨ p4) ∨ False)) ∨ (p4 → (((p1 → p4) → True) → True)))) → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218590623962807850224945683001 : (((p3 → True) → (p2 → p2)) → (((p1 ∧ ((p3 ∧ (p2 → p5)) → p2)) ∨ ((((p3 ∧ True) ∨ p5) ∨ (False ∧ False)) ∨ (True ∨ False))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_65725926919805523759597162485 : ((p4 ∨ (((p4 → ((False ∧ False) ∧ (p1 → (p1 ∧ (p2 → (p5 ∨ (p5 ∧ (True → p3)))))))) → ((p2 → True) ∧ False)) → (p5 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47602434464883093643143169651 : (((p3 → (False ∨ (((p2 ∨ (p5 → p2)) → (((True ∧ (p2 ∨ p4)) ∧ (p3 ∧ (True → p4))) → (p5 ∨ p5))) ∨ p1))) ∨ (False → p4)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65895973329877172812187421228 : ((p4 ∨ (False ∧ ((((False → p2) → (p4 ∨ (p1 ∧ ((((True ∨ p2) → p1) ∧ False) → p4)))) ∧ (p2 ∨ False)) ∧ (p2 ∨ (True ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248856907546078689479418569598 : ((p3 ∨ p4) ∨ (p5 → ((((p4 → False) ∧ p2) ∨ (((p2 ∨ ((p2 ∧ False) ∨ ((False ∧ p1) → p4))) ∧ ((True ∧ p5) ∧ p4)) ∨ p5)) ∧ True))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247545577700514880080942172841 : ((False ∨ p4) ∨ (((p4 ∧ p1) ∨ ((p5 ∨ p1) ∧ (True ∧ (p3 ∧ ((True → p1) ∧ ((p5 ∧ (p2 → p1)) ∧ p1)))))) → (False ∨ (p1 ∨ False)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h7.left
      let h21 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Conjunctions on the left can always be decomposed.
      let h28 := h26.left
      let h29 := h26.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43769326319236616897959667773 : ((((p5 ∧ (((p1 ∧ ((True → (True → (((p1 → p1) → (p3 → p2)) ∧ p3))) → (p4 ∧ (p5 ∧ p2)))) ∨ p5) ∨ True)) → p4) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39008211020204954094283789128 : ((((p4 ∨ True) ∧ (p1 → (p2 ∨ ((((((((False ∨ False) → p4) ∨ p1) → (p4 ∨ True)) → (True → p3)) ∧ p2) → True) → p5)))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38052555757500801041574138439 : (((((p5 ∨ ((((((p3 ∨ (False ∨ p2)) → False) ∧ True) → (p1 → p1)) ∧ True) → (False → False))) ∨ (p4 ∨ p5)) → (p5 ∨ p5)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310569679705188667497614214383 : (p2 ∨ ((((p3 ∧ True) ∧ True) → p3) ∧ (((((p3 → (p2 ∨ (p2 ∨ ((p5 ∧ p3) ∧ p3)))) → (False → (False ∧ p1))) → p2) ∧ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315717019384700929123106343000 : (p3 ∨ ((True → False) ∨ (p4 → (p3 ∨ ((p5 → (((((p3 → p5) ∧ True) ∨ (p1 → p5)) ∧ p1) ∨ p3)) ∨ (False → (p2 ∨ (p4 ∧ p5)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149976149298525809220053883826 : ((p4 ∨ (((((p1 → p2) ∧ p4) ∧ p3) ∧ p2) ∧ (((False → (p3 → True)) ∧ (p1 → (True ∧ p4))) ∨ p5))) ∨ (((p5 → p5) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148563086544858766844686678307 : ((((True ∧ p5) ∨ (p5 ∧ ((p3 ∨ (p2 ∨ p1)) ∧ True))) ∧ ((False ∧ (p5 → ((p2 → p2) ∨ p4))) ∧ p5)) ∨ (((True → p4) ∨ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186087501934274667496414050524 : ((((p5 ∧ (p1 → (p5 ∨ ((p3 → p4) → p1)))) → False) ∨ p4) → (((((p1 ∨ p4) ∧ (p2 → p3)) ∨ p3) ∧ True) ∨ (False → (True ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48963706681376274183920820668 : (((((((False ∨ (True ∧ (p5 → (False ∧ (True ∨ (p1 ∧ ((p2 → p2) → p5))))))) ∨ p2) ∧ p2) ∨ p4) ∨ p1) ∨ (p2 → (True ∨ p1))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247581902544589133361031359001 : ((False ∨ p4) ∨ (p5 → ((p4 ∧ ((p5 ∧ p4) ∨ ((((p3 ∨ p5) ∨ (False ∧ p2)) ∨ p1) → p1))) ∨ (True ∨ ((p2 ∧ p5) ∧ (p2 → False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705962957308688702441736882825 : (((((p4 ∧ (p1 → True)) → (p3 ∧ (p4 → True))) ∧ ((p5 → p1) ∧ (((p2 ∨ p4) ∨ p1) ∧ (p2 ∨ (((p3 ∨ p5) ∧ p1) ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51484090523473079583363670383 : ((((((True ∧ True) ∧ p2) ∧ (p5 ∨ p5)) → (((p4 → p3) ∧ (p3 ∧ p2)) → (p4 → p3))) → (((p1 ∨ p5) ∧ p1) ∧ (False → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166325734982162589313931894863 : ((p5 ∧ ((p3 → ((p1 ∧ p1) ∨ p1)) ∧ ((((p2 ∨ (p4 ∧ True)) ∧ False) ∨ p1) → p2))) ∨ ((((p5 → p1) → p3) ∨ (p4 → p4)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314128752871661502336895356059 : (p3 ∨ ((p3 ∧ ((((p5 → ((p4 ∧ True) ∨ p4)) ∨ p5) → p2) ∧ (p3 ∧ (p5 ∧ ((p1 ∨ (p4 ∨ p2)) → (False ∧ p4)))))) → (p2 ∧ False))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h10 : ((p5 → ((p4 ∧ True) ∨ p4)) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h11 := h4 h10
  -- One of the premise coincides with the conclusion.
  exact h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h13.left
  let h15 := h13.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h15.left
  let h17 := h15.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h17.left
  let h19 := h17.right
  -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
  have h20 : (p1 ∨ (p4 ∨ p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h21 : ((p5 → ((p4 ∧ True) ∨ p4)) ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h22 := h14 h21
    -- One of the premise coincides with the conclusion.
    exact h22
  -- We have shown the premise of h19, we can now drive its conclusion.
  let h23 := h19 h20
  -- We need to get the left conjuct of h23 based on <expert-advice>.
  let h24 := h23.left
  -- False on the left can always be used.
  apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171753144003361937216801328077 : ((((p2 → ((True → (((p2 ∧ True) → False) ∧ (p3 ∧ False))) ∧ False)) ∨ False) → False) ∨ (p5 ∨ (False → ((True ∧ ((p5 ∧ True) ∨ p3)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37452461138684549592184465986 : ((((((((True → False) → True) → (False ∨ p3)) ∧ ((True → p5) ∨ p4)) ∨ ((p3 ∧ ((p3 → p5) ∧ (False → p2))) → p5)) ∨ p5) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320480745765098001723177768472 : (p4 ∨ ((p3 → p1) → (((p5 → (p4 ∧ (p2 ∧ (((p4 ∧ False) ∨ p4) → ((p2 ∧ (p5 ∧ p2)) → ((p1 → p3) ∨ p5)))))) ∨ True) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169419878435351439939038088562 : ((((p2 ∨ (True ∧ ((p5 → p1) ∧ (p1 ∧ ((False → p5) → p2))))) → p2) ∨ p4) ∧ (p2 → (True ∧ ((p4 ∨ ((p5 ∧ p3) ∨ p4)) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : (False → p5) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h12 := h9 h10
    -- One of the premise coincides with the conclusion.
    exact h12
  -- Implications on the right can always be decomposed.
  intro h13
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679156851331048220454618118272 : ((((p4 ∨ ((((((p3 ∧ (p1 → (False → p5))) ∨ p4) → (p4 → False)) ∧ (p1 → p3)) ∨ p1) ∨ p1)) ∨ (False → (p1 ∨ (p4 ∧ True)))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_112663877594718035817016050377 : ((((((p4 → (((True ∧ True) ∨ p1) ∧ (False ∧ p4))) → p3) ∨ (((p4 ∨ p1) ∨ p2) ∨ False)) ∨ (p5 ∧ (p3 → p2))) → p5) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119591821622078722812806330647 : ((p5 → (False ∧ ((((((True ∨ False) ∧ p4) ∧ (p3 → (True ∧ True))) ∨ ((False → (p5 ∧ p5)) ∧ p5)) → (p3 ∧ p4)) ∨ False))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_451029652020217775863068550273 : (((((p5 ∨ (False ∨ ((False ∧ p4) ∧ (p5 ∧ ((p5 ∧ p2) ∧ (((p4 ∨ True) → True) → False)))))) ∨ True) ∨ (p2 ∧ (p4 ∧ (p5 ∨ p1)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60381849631720525398208754510 : (((p3 → p2) → ((((False ∨ (p4 → True)) ∧ p1) → p5) ∨ (p4 ∨ ((False → (p3 ∨ ((False → (False ∧ (True ∨ p5))) ∨ p2))) ∨ True)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_586229771070966466249543093734 : (((((((p1 → (p1 ∧ ((p4 ∨ p5) → (False ∧ p1)))) ∨ p1) ∧ (p1 ∨ (((True ∧ False) ∧ (p4 ∧ True)) → (p4 ∨ p3)))) ∧ True) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191080398612616632727682334983 : ((((False ∨ p1) ∧ p4) ∧ (p3 → ((p4 ∧ p3) ∨ True))) ∨ (p2 ∨ (False → (p5 ∨ ((((False ∨ True) ∧ p5) → (p5 → p4)) → (False ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118618880925744674096568392400 : ((p4 ∨ ((p3 → (((p5 ∧ p4) ∨ (p3 ∧ (p1 ∧ p2))) ∧ False)) ∧ (((True ∧ (p5 → ((p4 → p4) ∧ p3))) ∧ p1) ∨ True))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149585764534804659859612448110 : ((p3 ∧ (((True → False) ∨ ((p4 → ((p3 ∨ (True → ((False ∨ p4) ∨ (p5 → p1)))) → False)) → p5)) ∨ p5)) ∨ (((p3 → p4) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136943323964343527215141215445 : (((p4 → p5) ∨ ((p2 ∨ (p3 ∧ (p4 ∨ (((False ∨ (p1 ∧ False)) → p3) ∧ p3)))) ∨ (p3 ∧ (p5 → (False ∧ p2))))) ∨ (p1 → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208039894955108559545022953653 : (((p3 ∧ (False ∨ p5)) ∨ (p1 → p1)) → ((p1 ∧ p3) ∨ (p2 → ((p1 ∨ p3) ∨ ((p4 ∨ (p4 ∨ ((False → p2) ∨ (p4 → p1)))) ∨ p2))))) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253787353176203392023092457465 : ((p1 ∧ p2) → ((p4 ∨ (((False ∨ True) → ((p3 → (((((p2 ∧ p3) ∨ (p4 ∨ (p5 ∨ p2))) → True) → p3) ∨ True)) → p4)) ∨ False)) ∨ True)) := by
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
theorem thm_5_vars_607966967137164025595283037042 : (((((p3 → (((False ∧ ((p4 → p2) → ((p3 → ((p3 ∨ p1) → ((p1 ∨ p4) ∧ p5))) → (p3 → p2)))) ∧ False) ∧ p1)) ∧ True) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671424990414126998686843331195 : ((((p1 → ((p2 ∨ p2) ∧ (((((p5 → p5) ∨ (False → False)) → True) ∨ ((p1 ∨ p5) ∨ (p4 ∧ p5))) → False))) ∨ ((p4 → p1) → True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232988521196648030415330086887 : ((p3 ∧ (p3 → p5)) → (((((True ∨ p3) ∨ (p5 ∧ (True → (p2 → (p5 ∨ (p2 ∧ (p4 ∧ True))))))) ∨ (p5 ∨ True)) → (p5 ∧ p4)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382784439372231782057575175115 : ((((((p5 ∨ p5) ∧ (((True → (p5 ∧ p1)) ∨ (False ∧ (p1 → True))) ∨ (((False ∧ ((False ∨ p5) ∧ False)) → p5) ∨ p4))) ∨ p5) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_157674855173686938959403686126 : ((((p2 ∧ (False → p1)) → ((((False ∨ p2) ∧ True) → False) → (p3 ∨ p5))) ∨ (p1 ∧ (p5 ∨ p4))) ∨ (p2 ∧ ((p3 ∧ p4) ∨ (p1 → True)))) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : ((False ∨ p2) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111321261521133572982537220872 : (((p1 ∧ (p1 ∧ (((p3 ∨ (p2 → (((p2 ∨ (((p4 → p2) → p1) → (p1 ∧ True))) ∧ p2) → p4))) → p1) ∨ False))) ∧ p3) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206812626006039778147744324416 : ((p5 → ((False ∨ (p2 ∨ p2)) ∨ p1)) ∨ (((p4 ∧ p2) → ((p2 ∨ True) ∧ ((((p5 → (p4 ∧ p1)) ∧ p1) ∧ (True ∨ p3)) → p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191633029820090913748068974452 : ((p4 ∧ (((p3 → ((p3 ∧ p4) → p4)) ∨ True) ∨ p5)) ∨ (((p2 → ((p3 ∨ (p1 → (((p2 ∧ False) → p4) ∧ p3))) ∧ p5)) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197487022005229621484453316343 : (((True ∧ (p4 ∧ (p3 ∨ p2))) ∧ (p1 ∨ True)) ∨ (True ∧ (p5 → (((p4 ∨ p4) ∧ ((p1 ∨ (p5 ∧ False)) ∨ True)) ∨ (p2 → (False → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719416310559077091290762508258 : ((((False ∨ (p5 ∧ (False ∨ p4))) ∨ (p4 ∨ (((p3 → (p2 ∨ p4)) ∧ p4) → (p1 → ((p1 ∧ p4) ∧ ((True ∨ p2) ∧ (True → p4))))))) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721466193083420735658154261458 : ((((p2 ∧ ((p5 → p1) ∧ p5)) → (((p1 ∨ False) → ((((False ∧ p3) ∨ ((p3 ∨ True) ∧ True)) → p2) → (p4 → (p3 ∧ p4)))) ∨ p2)) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345642434228916418374192136211 : (p3 → ((p3 ∧ ((((True ∧ ((p5 → p1) ∧ True)) → p4) ∨ ((p2 → ((p4 ∧ (p2 ∧ (True ∧ (p5 ∧ p5)))) → p5)) ∧ True)) → p2)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115632637221334092278612502683 : ((((True → (p3 ∧ (False ∨ p4))) ∧ False) ∨ ((((p3 ∧ p2) ∨ p3) ∧ ((((p3 ∧ False) → p4) ∨ p2) ∧ p4)) → (p3 ∧ p3))) ∨ (p5 ∨ p2)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h17.left
    let h22 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h23 =>
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h24 =>
      -- One of the premise coincides with the conclusion.
      exact h19
  case inr h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h17.left
    let h27 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h28 =>
      -- One of the premise coincides with the conclusion.
      exact h25
    case inr h29 =>
      -- One of the premise coincides with the conclusion.
      exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356536003388371092560416172062 : (p5 → (((True → p4) ∧ ((p3 ∨ p3) ∧ ((p5 ∧ p2) ∨ p2))) ∨ (((p3 ∨ p5) ∨ p2) ∧ (p1 → (p5 → ((False ∧ p2) → (p3 ∨ p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116749090070043177905273313274 : (((p5 ∧ False) ∨ ((p3 ∧ (p1 ∧ False)) ∨ (p5 ∨ (((True ∨ p5) → ((True → ((p4 ∧ True) → (p5 → p5))) → False)) ∨ p5)))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53410247864144382717874889828 : ((((p3 ∧ (((p4 → p1) → (False ∨ p5)) ∨ p3)) → (p5 ∨ False)) → ((p3 ∨ (((p4 → (p5 ∨ (p1 ∨ p2))) ∧ False) ∨ p5)) → p5)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (p3 ∧ (((p4 → p1) → (False ∨ p5)) ∨ p3)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59599453896245425555955427726 : (((p4 → p3) ∨ (((True ∧ ((((p2 ∧ False) ∧ ((p5 ∧ False) ∧ p4)) ∨ True) ∧ False)) ∨ (p5 → p2)) ∧ (p5 ∨ ((p5 ∧ p3) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138832779761370151919273934465 : (((p3 ∧ (p5 → (p5 → (p2 ∨ ((((False ∨ p3) → p5) → p3) → ((p1 ∨ p4) ∧ ((True ∨ p2) ∧ p5))))))) ∧ p1) → ((p4 → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47458736747428006389532536950 : (((p4 ∧ (p4 ∧ (((p3 ∨ (False ∨ (True → ((p5 ∨ ((p3 → (p3 ∨ p4)) ∧ p2)) → p5)))) ∨ p4) ∨ (p3 → False)))) ∨ (False → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788247811787399781581429689709 : (((p5 ∨ ((p3 ∨ ((((((p3 ∧ True) → True) ∨ (((p1 ∨ p5) ∨ (False ∨ (p4 → p3))) ∧ p1)) → p2) ∨ (p1 ∨ p5)) → p3)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339627558908890569635325811563 : (p1 → (p2 ∨ (((p3 → ((p5 ∧ p3) ∨ (p3 ∨ False))) ∧ p3) ∨ (((p5 ∧ p2) ∧ p4) ∨ ((p4 ∧ False) ∨ (True ∧ (p5 → (True ∨ p3)))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234216340112739092226362640916 : ((False → (p5 ∧ False)) → (((True ∧ p5) ∧ (p5 → p2)) → ((((True ∨ p1) ∨ p2) → p1) → (((p1 → False) → p5) ∧ (p3 ∨ (p2 ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h13 : ((True ∨ p1) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h14 := h3 h13
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217984590938101640544387972805 : (((p4 ∧ True) ∧ (p4 → p1)) → ((((p3 ∨ False) ∨ (p3 ∧ ((False → p2) ∨ p2))) ∧ (((((True ∧ p4) ∨ False) ∨ p2) → True) → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69381659003967952985063519638 : ((p5 → (p1 → (((p4 ∧ (((p5 → ((p3 ∨ p1) ∧ p1)) ∨ (False → p2)) ∧ p1)) → False) ∨ (((p4 ∧ p2) → False) ∧ (True ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197160988417895103433343814042 : (((p4 → ((True → (p1 → p1)) → False)) ∨ p1) ∨ ((False ∨ (p5 ∧ (True → p1))) → ((p5 ∧ ((p5 ∨ ((p4 → p4) → p1)) ∧ p2)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693727870890833014452783205807 : (((((p1 ∨ (((p5 → p4) → ((p4 ∨ (p1 → p1)) ∧ True)) → False)) ∨ p5) ∨ ((p4 → p1) ∧ ((p1 → (False ∧ p4)) → (p1 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52248357355252181844537123738 : (((False ∨ (((p4 → ((p2 ∧ ((p2 ∧ (p2 ∨ p5)) ∨ p3)) → p3)) ∨ p2) ∨ p4)) → ((False ∧ p4) ∨ (True ∨ ((p1 ∧ p2) ∧ p1)))) ∨ p3) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65340373746397770196761735465 : ((p3 ∨ (((p3 ∨ ((((p5 → True) ∧ p3) ∧ p4) ∨ (p4 → ((True ∨ p2) ∨ True)))) → False) ∧ (p3 ∨ ((p1 → p2) ∨ (False ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47811617232725330048316081599 : ((((((p2 ∨ (((p3 ∨ (p4 ∧ p1)) → False) → (False ∨ p2))) ∨ (p2 ∧ (p1 ∨ p5))) → ((p5 ∧ p3) ∨ p1)) → p5) → (p1 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57607545082486536969289728634 : ((((p4 → True) ∧ p4) → (p1 → (((((p2 → p1) ∨ p1) ∧ p5) → ((p4 → p2) ∨ (p3 ∨ False))) → ((False ∨ p1) → (p2 ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321621388618241341846752785016 : (p4 ∨ (p3 → (((p5 ∧ (p2 ∨ p3)) ∨ (False ∨ (True → p5))) ∨ ((True ∨ (False → (p3 → (p1 ∨ p4)))) ∨ ((True → (p3 ∧ p1)) → p4))))) := by
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
theorem thm_5_vars_692711469807872724975459158052 : ((((((p1 ∧ (True ∧ True)) → (p4 ∧ p5)) → ((False → (p2 → p2)) → False)) ∧ (((p3 → p5) ∧ p2) → ((p3 ∧ False) ∨ (p1 ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616320399556347243908532566758 : ((((((p4 → (p3 ∨ False)) ∨ (p2 ∨ ((p1 ∨ (True ∧ p5)) ∧ p1))) ∨ ((((p4 ∧ (p4 → (p2 ∨ p4))) ∧ p4) ∨ True) → True)) ∨ p4) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657989011822081949517185596415 : ((((p2 ∧ (((((p2 → p5) ∧ p1) ∨ ((False → p4) ∧ (p4 → ((True → p2) ∨ True)))) → False) ∨ ((p2 ∧ p2) → False))) ∨ (p2 → p2)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244554023854393487826189548724 : ((False ∧ p4) ∨ ((((True → False) → ((((p4 ∨ p3) → ((p3 ∧ p3) ∨ False)) ∨ p3) ∨ True)) ∨ (p3 ∨ (p1 ∨ ((p4 ∨ False) ∨ p2)))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_663055370336486592111843369691 : (((((p5 → (p3 ∨ True)) → ((p5 ∨ ((p2 ∨ True) → ((p5 ∧ p1) ∨ p2))) ∨ (((p2 ∨ p2) ∨ p4) ∧ (p4 → p1)))) → (True ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607054105595469044368121413 : (((((((False ∨ ((p2 ∨ p1) ∨ p2)) → (False ∨ (p4 ∨ p1))) ∧ ((p5 ∧ False) ∧ (p5 ∧ False))) → True) → p2) ∧ (True → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758902712880462469210556457163 : (((p2 ∧ ((((p4 → (((p1 ∧ p3) ∨ False) ∧ (True ∧ p5))) ∨ ((p2 ∧ ((p3 → p2) → p5)) ∧ p1)) ∧ (p5 → (True ∧ False))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46373254838481608913410739841 : (((((p5 → (p1 → (p1 ∨ (p2 ∧ p1)))) → ((False ∨ p3) ∨ p2)) → (False ∧ (((p2 ∧ p5) ∧ (p2 → p1)) ∧ False))) ∧ (p3 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356047599103386821065128109437 : (p5 → ((p2 ∨ (p3 → (((((False → p4) ∧ p1) ∧ (False ∨ p2)) ∨ (False ∨ p5)) ∧ ((p3 ∧ True) ∨ p2)))) ∨ ((p1 ∨ p5) → (p4 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116866395189925703858073752998 : (((p1 → p5) ∨ (((p4 ∧ ((((((p4 → p1) ∨ (p4 → False)) ∧ ((True → p2) ∨ p4)) ∧ p1) ∨ p1) ∨ p3)) → p3) ∨ p3)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789266759660481827302495320256 : (((p5 ∨ (((((p4 → (p3 ∧ p2)) ∧ (True ∨ (p4 → True))) ∨ (p2 → ((p4 ∨ p4) ∨ p3))) → p3) → (p3 ∨ (False → (p1 ∨ p1))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



