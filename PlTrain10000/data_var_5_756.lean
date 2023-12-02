variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252145484822214724156095981994 : ((p4 → p3) ∨ ((((p2 ∨ (((p1 → True) ∨ False) → (p1 ∨ p5))) ∧ p4) ∨ (False → (((p5 → p1) ∧ p1) ∧ ((p1 ∧ p2) ∨ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171480005882804966694589253221 : (((p5 ∨ ((p5 ∧ (p1 ∧ p5)) ∨ ((((True ∨ p3) → p4) → p2) ∧ p1))) ∧ p1) ∨ ((p3 → True) ∧ ((((p5 ∧ p2) ∧ p1) ∨ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123716306432409198967103220902 : ((((p2 ∨ (p5 → ((False → (p2 ∧ p3)) ∧ (p5 ∧ (p2 ∨ True))))) → p2) ∧ (((p5 ∨ p1) ∧ ((p3 ∧ p5) ∧ p3)) ∧ p1)) → (p2 ∧ p3)) := by
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
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : (p2 ∨ (p5 → ((False → (p2 ∧ p3)) ∧ (p5 ∧ (p2 ∨ True))))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h15
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h15
      -- False on the left can always be used.
      apply False.elim h15
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h14
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h16 := h2 h13
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h7.left
    let h19 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h22 : (p2 ∨ (p5 → ((False → (p2 ∧ p3)) ∧ (p5 ∧ (p2 ∨ True))))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h24
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h24
      -- False on the left can always be used.
      apply False.elim h24
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h23
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h25 := h2 h22
    -- One of the premise coincides with the conclusion.
    exact h25
  -- Conjunctions on the left can always be decomposed.
  let h26 := h1.left
  let h27 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h28 := h27.left
  let h29 := h27.right
  -- Conjunctions on the left can always be decomposed.
  let h30 := h28.left
  let h31 := h28.right
  -- Disjunctions on the left can always be decomposed.
  cases h30
  case inl h32 =>
    -- Conjunctions on the left can always be decomposed.
    let h33 := h31.left
    let h34 := h31.right
    -- Conjunctions on the left can always be decomposed.
    let h35 := h33.left
    let h36 := h33.right
    -- One of the premise coincides with the conclusion.
    exact h34
  case inr h37 =>
    -- Conjunctions on the left can always be decomposed.
    let h38 := h31.left
    let h39 := h31.right
    -- Conjunctions on the left can always be decomposed.
    let h40 := h38.left
    let h41 := h38.right
    -- One of the premise coincides with the conclusion.
    exact h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190090629776756138264614174517 : ((((((p1 ∧ p1) ∨ p3) ∧ p1) ∨ (False → True)) ∧ False) ∨ ((p2 ∧ (((p3 → p3) → (p2 ∧ p3)) → ((p1 ∨ p4) ∧ (p4 ∧ p1)))) → p2)) := by
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
theorem thm_5_vars_775790687927731382109770261065 : (((False ∨ (p5 ∨ ((((((p1 ∧ (p5 ∧ (p1 ∨ p2))) ∧ ((((p2 ∨ (p1 ∨ False)) ∧ p1) ∨ p2) → p1)) → p4) ∨ p4) ∨ p5) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50202044615160132299067064417 : (((((False ∧ (((p3 ∨ p2) ∨ (True → p3)) ∨ (((p2 → p3) → p2) ∧ (p2 → p2)))) ∧ p4) ∨ True) ∨ ((p2 → (p4 ∨ p5)) ∧ p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316743787515385622305107358789 : (p3 ∨ (True → (((p4 → ((p4 ∧ True) → ((((p4 → p1) ∧ p5) ∧ (True ∧ p3)) → p1))) ∨ ((p2 ∨ p4) ∧ (p3 ∧ False))) → (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
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
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h7.left
      let h13 := h7.right
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54464387465819939346541948607 : ((((False → ((p2 ∨ True) ∧ (p5 → True))) → p3) ∨ (((p2 → ((p4 ∨ (p4 ∧ p3)) → p3)) → False) → ((True → p1) → (p2 → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187390087716270992827419668341 : ((p4 ∧ (((((p5 → (p1 → p5)) ∧ p3) ∨ p3) ∨ True) → p5)) → ((p2 → (p5 ∧ (True ∧ p3))) ∨ ((((True → p3) ∨ p2) → True) → True))) := by
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
theorem thm_5_vars_136167513615012766158115422024 : (((p4 → (False → ((p5 ∨ p5) ∨ (p5 ∨ True)))) → (((False ∨ (((p2 ∧ p3) ∨ p1) → (p5 ∨ p4))) → True) ∧ p3)) ∨ (True ∨ (p2 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119524725314175652347073428311 : ((p5 → ((p4 ∧ (((p5 → (((((p4 → p5) ∨ (False ∨ p3)) ∧ False) ∧ (p4 ∨ (p1 → p5))) → p1)) ∨ p4) → p4)) ∨ True)) ∨ (p4 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174121678942436899712514795077 : (((True → (((False → True) → p2) ∨ (p5 ∧ (p1 ∨ (True ∧ p5))))) ∧ (p2 ∧ p1)) → (False ∨ (((p2 ∨ True) ∧ ((True → p3) ∨ p3)) ∨ p2))) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157338356327357476995806583997 : (((p2 ∨ ((((p5 ∧ p4) ∨ (False ∧ True)) → (True ∧ p5)) ∨ (p2 ∧ ((True ∧ p5) → p3)))) → p1) ∨ (True ∨ ((p5 → p4) → (True ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197637582482172919931980674087 : ((((True ∨ (True ∨ False)) ∨ p4) → (p2 ∨ p1)) ∨ ((p5 → True) ∨ ((((False ∧ (p4 ∨ (p1 ∨ p2))) ∧ (p3 ∧ (p5 ∨ False))) → p2) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340857882839845059082696950252 : (p2 → (((False → ((True ∧ (p2 → ((((((p3 → (p2 ∧ False)) ∨ p1) ∨ p2) → False) ∨ p2) ∨ p2))) ∨ p3)) → ((p3 ∧ p3) ∧ True)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681423976645702979648763012503 : ((((p3 ∨ (((p1 ∧ (((((p3 ∧ p1) → p1) ∨ True) → p4) ∨ p4)) → p2) ∨ ((False → p3) ∨ p2))) → (p2 ∨ ((p2 ∧ p3) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40935307032437693014937936031 : (((((((p1 ∨ p1) → (p4 → ((p1 ∨ (p5 → (p3 ∧ (p5 → p3)))) ∧ (p4 ∧ p4)))) → (p5 ∧ p5)) ∨ p5) ∨ (True ∨ p2)) ∨ p4) ∨ p4) := by
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
theorem thm_5_vars_669750533780461555442650022666 : (((((((True → True) → ((((p4 ∧ p1) ∨ p5) ∧ p1) → (p2 → p1))) → p5) ∨ (p4 ∧ (p2 ∨ (False ∨ p3)))) ∨ (True ∨ (p1 ∨ True))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_158410785375953309518476091224 : (((p1 ∧ p1) ∨ ((p2 ∧ (p1 → (p3 ∨ False))) ∧ (p2 → (((p4 → (p3 → True)) ∧ p1) ∧ p4)))) ∨ ((False ∨ (p5 ∧ p2)) → (False ∨ p2))) := by
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
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207203267662480833786497896246 : ((((p4 ∧ (p1 ∨ p4)) ∧ p4) ∨ p2) → (((p1 ∧ p5) ∧ p4) ∨ (True ∨ (False ∧ (((p3 ∧ (True ∧ True)) ∧ True) ∨ ((p3 ∧ False) ∨ False)))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232880751229150096796532292113 : ((p2 ∧ (p5 → p3)) → (p3 → (((p5 → p2) ∨ ((p4 → p4) ∨ (True ∧ True))) → (((p2 → True) → (p5 ∧ ((p3 ∨ p4) → p3))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h1.left
      let h10 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h1.left
      let h15 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116551842297014730550985318207 : (((p1 ∨ p1) ∧ ((p5 → (((p3 ∨ False) ∨ ((p2 ∨ False) ∨ ((p5 → True) ∧ p1))) ∨ (p5 ∨ (False ∧ p1)))) ∨ (p4 ∨ True))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53246697557941143711012204007 : ((((p1 ∧ p2) ∧ (((((p1 → False) ∧ p3) ∧ p3) ∨ p3) ∨ p5)) ∨ ((True ∨ True) ∨ (p5 ∧ (((True ∧ p2) ∨ (p1 ∧ p1)) ∧ p3)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61642979632881542426563690189 : ((p1 ∧ (False ∧ ((((True ∨ (p3 → p2)) → ((p4 ∧ ((p5 ∧ (p5 ∧ p2)) ∨ ((p1 → True) ∨ (p5 ∧ p2)))) ∧ p1)) → False) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18928380114618214189108904206 : (((p4 ∧ (((True ∧ p3) ∨ (p5 → ((p4 → (False ∨ False)) → (True ∨ p4)))) → (p4 ∧ p3))) ∨ (p1 → (p4 ∨ (True → (True ∨ p4))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56647594994735946835160231320 : ((((p1 ∨ p4) ∧ p4) ∧ (((False ∧ ((p5 ∧ p1) → (p2 ∨ (p2 ∨ p5)))) ∨ (p5 ∧ ((p1 → (p4 ∨ False)) ∧ p4))) ∨ (p2 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47839261152806121686905984907 : ((((p2 ∧ (((((p5 ∨ p5) → (p1 ∧ ((p2 → p2) ∨ (p2 ∨ (p5 ∨ (p4 ∧ p5)))))) ∨ False) → p5) ∨ True)) → p3) → (p4 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343553393123563377049909141006 : (p2 → ((p2 ∨ p4) → ((((((True ∨ p5) → ((p3 ∧ p2) ∧ (True ∧ False))) ∧ ((((p3 ∧ p4) → True) → p5) → p3)) ∧ p2) ∧ p4) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263996435117851732254914307912 : (True ∧ ((p2 → (p4 ∨ (((p4 → (p4 → (p2 ∨ p1))) → False) ∧ p1))) ∨ ((False → True) → (p1 → ((p5 ∧ p5) ∨ ((p4 ∧ p5) ∨ True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704784159190827852744112762166 : ((((p5 ∧ ((p1 ∧ ((False ∧ p2) → p4)) ∧ (p4 ∨ True))) → (((False → True) → (p2 → p3)) ∨ ((p2 ∨ (p2 → p3)) ∨ (p3 → True)))) ∨ False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116182533183475383423378604360 : (((p4 → (p1 ∨ p3)) ∧ ((p5 → ((((p4 → ((p5 → (p1 → True)) → p5)) ∧ (False ∨ p5)) ∧ p2) → p1)) ∨ (p4 → True))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181719871268682688682525296648 : ((p5 → (p5 → (((p2 → (False → False)) ∧ False) ∨ ((False → p1) ∧ p2)))) → ((((p3 ∧ p2) ∨ (False → False)) → False) ∨ (p3 ∨ (False → p2)))) := by
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
theorem thm_5_vars_149413446766779700393599534070 : ((True ∧ (((False → False) → ((p3 ∨ (p5 ∨ (p3 ∨ p2))) ∨ p3)) ∨ ((False ∨ (p2 ∨ (p3 ∧ p4))) → True))) ∨ (True → (True ∨ (p5 ∨ p1)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689433083160010645283295024025 : ((((((p1 ∨ False) ∧ ((p3 ∨ (False → True)) ∨ (p3 → p3))) ∧ (p2 ∧ (p3 → p2))) ∨ (((p2 → p5) ∧ (p2 → p2)) → (True → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681745765818802823277287553468 : (((((((((p4 → (p2 ∨ p5)) ∧ (p3 ∨ (p5 ∧ p4))) → False) ∧ (p5 → p5)) ∨ p5) ∧ True) ∧ ((False ∧ ((False → p2) ∧ p1)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353534918105682591766065769744 : (p4 → (p3 ∨ (((p1 → p3) → (p4 → ((p1 ∨ (False ∨ (p1 → (((p3 → p4) ∨ True) ∧ p2)))) ∨ ((p5 → (False ∨ False)) ∧ True)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306030130722923172803562782004 : (p1 ∨ ((((p4 ∨ p5) → False) ∧ p4) → ((p3 ∧ ((((((p3 ∧ p4) → p3) ∨ p4) ∨ p2) ∨ (p4 → p5)) ∨ (True ∧ p1))) ∨ (p5 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p4 ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242174095262277046327184787721 : ((p2 → True) ∧ (p1 → (p4 ∨ ((((p5 ∨ p1) ∧ ((True ∧ p3) ∨ (p4 ∨ p3))) ∧ (p5 → False)) ∨ (True → (p1 → ((p2 → p4) ∨ p1))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59411982624268481980358672100 : (((True → p5) ∨ ((False ∧ ((((False → p1) ∨ (p2 ∨ (p3 ∧ ((p2 → False) ∨ p5)))) → (p4 ∧ p5)) → ((p4 → False) ∧ True))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616449419578335091198775702272 : (((((((((p4 ∧ p4) ∧ False) ∨ p3) ∧ p5) → (True ∨ (p3 → p1))) → (p1 ∧ ((p5 → (p2 ∨ (p2 → (False ∨ p4)))) ∧ p4))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308401539363202591565275239105 : (p2 ∨ (((p4 ∨ ((True ∧ (p5 → p1)) → (True → ((p3 ∧ p5) ∨ (p1 ∧ ((((True ∧ False) → True) → (p3 → p5)) ∧ False)))))) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53166034846329147228305978886 : ((((p5 → (((p1 → False) → p1) ∧ (p5 ∧ (p5 ∨ False)))) ∨ False) ∨ (False ∨ (((p3 ∨ False) ∨ p5) ∧ ((p5 ∧ (p5 ∨ False)) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_812674147896216735114570260256 : ((((((p4 → ((p4 → (p3 ∨ ((p1 ∨ ((False ∨ False) → p3)) → p4))) → p3)) ∧ ((p1 ∨ (True ∧ (p5 → p4))) ∧ p4)) ∧ p4) ∧ p1) → p3) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h11 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h12 := h6 h11
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : (p4 → (p3 ∨ ((p1 ∨ ((False ∨ False) → p3)) → p4))) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h14
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h18 := h12 h13
    -- One of the premise coincides with the conclusion.
    exact h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h22 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h23 := h6 h22
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h24 : (p4 → (p3 ∨ ((p1 ∨ ((False ∨ False) → p3)) → p4))) := by
      -- Implications on the right can always be decomposed.
      intro h25
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h26
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h28 =>
        -- One of the premise coincides with the conclusion.
        exact h25
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h29 := h23 h24
    -- One of the premise coincides with the conclusion.
    exact h29
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39781246697578351695860109098 : (((True → (p4 ∨ (p4 ∨ ((p2 → ((p5 ∨ p5) ∨ ((True ∨ p2) → p3))) ∨ ((p1 → ((p3 ∧ (p5 ∨ False)) → p1)) ∨ p1))))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342271461228023438344866249550 : (p2 → ((((p2 → False) → (p2 → ((p1 → p3) → (p4 ∨ (p1 ∨ ((p4 ∧ p4) ∨ p1)))))) ∧ False) ∨ (((p2 → p1) ∧ p5) ∨ (p4 ∨ p2)))) := by
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
theorem thm_5_vars_340736447047468833923024165500 : (p2 → ((((((True ∧ (True ∧ p2)) → (p5 → ((p3 ∨ (((p3 ∨ False) → p4) ∨ p1)) ∧ (p4 ∧ p2)))) ∨ (p1 ∨ p3)) → p3) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118874725210749239926533640896 : ((True → ((p2 → True) ∧ ((p4 → p3) ∨ (((((((p1 ∧ p5) ∧ False) ∨ p3) → p1) → p3) → p1) → ((p1 → True) ∧ p5))))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194277318082339034217196769744 : ((p5 → ((False ∨ p2) ∨ (((p4 → p5) ∧ p1) ∨ p3))) → (((False ∨ (p4 ∨ p1)) ∨ (((True ∨ (False ∧ p1)) → p4) ∧ p2)) ∨ (True ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217379593591754417730354235593 : (((p5 ∨ (p3 ∧ p5)) ∨ p5) → (False ∨ (((p1 → p5) ∧ (p4 → (p1 ∧ p5))) ∨ ((p1 ∨ False) ∨ ((p2 → p3) ∨ (p5 ∨ (p2 ∨ False))))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208995506763311825027699737689 : ((False ∨ (((True → p3) ∧ p1) ∨ p5)) → ((((True ∨ p3) ∨ False) → (((((False → (p1 ∧ p1)) ∨ p3) ∧ p5) → p4) ∨ (True ∨ p4))) ∨ p4)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h10 =>
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660077306683385823184678391673 : (((((((p3 ∨ (p3 ∨ (p1 ∨ (True ∧ p2)))) ∧ (((False ∨ ((p5 ∨ p2) → p2)) ∧ False) ∧ p5)) → (True → p2)) ∨ p3) → (p1 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190172257355416450764571956531 : (((p3 ∧ ((p1 ∧ ((p2 ∨ False) ∧ p5)) ∨ p2)) ∧ p1) ∨ ((((p5 ∨ (p3 ∨ True)) ∧ p3) ∨ (p2 ∧ ((p1 ∧ (True ∧ p1)) ∧ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342276284522513828294236852317 : (p2 → (((((p4 ∨ ((p1 ∧ ((p2 ∨ (True → p2)) ∨ p2)) ∧ False)) → (p1 ∨ p1)) ∧ p1) → False) ∨ ((((p4 → False) → True) ∧ p5) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721117052605238741142705694645 : (((((p4 ∨ p5) ∨ (p2 ∨ p5)) → (False ∨ ((p1 ∨ (((True ∨ p2) ∧ ((p2 ∧ (False ∧ (p3 ∧ (p2 → True)))) ∧ p1)) → False)) ∧ True))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h6.left
        let h9 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h8.left
        let h11 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- False on the left can always be used.
        apply False.elim h12
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h6.left
        let h16 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h15.left
        let h18 := h15.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- False on the left can always be used.
        apply False.elim h19
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h24.left
        let h27 := h24.right
        -- Conjunctions on the left can always be decomposed.
        let h28 := h26.left
        let h29 := h26.right
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- False on the left can always be used.
        apply False.elim h30
      case inr h32 =>
        -- Conjunctions on the left can always be decomposed.
        let h33 := h24.left
        let h34 := h24.right
        -- Conjunctions on the left can always be decomposed.
        let h35 := h33.left
        let h36 := h33.right
        -- Conjunctions on the left can always be decomposed.
        let h37 := h36.left
        let h38 := h36.right
        -- False on the left can always be used.
        apply False.elim h37
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h39 =>
    -- Disjunctions on the left can always be decomposed.
    cases h39
    case inl h40 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h41
      -- Conjunctions on the left can always be decomposed.
      let h42 := h41.left
      let h43 := h41.right
      -- Disjunctions on the left can always be decomposed.
      cases h42
      case inl h44 =>
        -- Conjunctions on the left can always be decomposed.
        let h45 := h43.left
        let h46 := h43.right
        -- Conjunctions on the left can always be decomposed.
        let h47 := h45.left
        let h48 := h45.right
        -- Conjunctions on the left can always be decomposed.
        let h49 := h48.left
        let h50 := h48.right
        -- False on the left can always be used.
        apply False.elim h49
      case inr h51 =>
        -- Conjunctions on the left can always be decomposed.
        let h52 := h43.left
        let h53 := h43.right
        -- Conjunctions on the left can always be decomposed.
        let h54 := h52.left
        let h55 := h52.right
        -- Conjunctions on the left can always be decomposed.
        let h56 := h55.left
        let h57 := h55.right
        -- False on the left can always be used.
        apply False.elim h56
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h58 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h59
      -- Conjunctions on the left can always be decomposed.
      let h60 := h59.left
      let h61 := h59.right
      -- Disjunctions on the left can always be decomposed.
      cases h60
      case inl h62 =>
        -- Conjunctions on the left can always be decomposed.
        let h63 := h61.left
        let h64 := h61.right
        -- Conjunctions on the left can always be decomposed.
        let h65 := h63.left
        let h66 := h63.right
        -- Conjunctions on the left can always be decomposed.
        let h67 := h66.left
        let h68 := h66.right
        -- False on the left can always be used.
        apply False.elim h67
      case inr h69 =>
        -- Conjunctions on the left can always be decomposed.
        let h70 := h61.left
        let h71 := h61.right
        -- Conjunctions on the left can always be decomposed.
        let h72 := h70.left
        let h73 := h70.right
        -- Conjunctions on the left can always be decomposed.
        let h74 := h73.left
        let h75 := h73.right
        -- False on the left can always be used.
        apply False.elim h74
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56952156755627917744674243097 : (((p1 ∨ (p4 → True)) ∧ (((p5 ∧ (False ∨ True)) ∨ ((False ∧ p4) ∨ True)) ∧ ((((p5 ∧ p3) ∧ ((p2 ∧ p4) ∧ p5)) ∨ True) → True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130140554819918989917109408018 : ((((((p2 → False) ∧ p1) ∨ (p5 ∧ p2)) → (((p5 ∨ p5) → (p4 ∧ ((True → False) ∨ True))) ∨ True)) ∨ (p4 ∨ p4)) ∧ (p4 ∨ (True ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
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
theorem thm_5_vars_3920112111809562952993711169 : (False ∨ (((p3 ∧ (p4 ∧ (((p4 ∨ True) ∧ True) ∨ (((p1 ∧ p5) → (p2 ∨ True)) → True)))) ∨ False) ∨ ((p1 → (p4 → p5)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231721721020202610408371325921 : (((p2 ∧ p2) → p3) → (((((True ∧ p3) → (p2 → (p5 ∧ (p1 → (p5 ∧ True))))) ∧ p1) ∨ (True ∧ ((True → (p2 → True)) ∨ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305000226947051579543458452018 : (p1 ∨ ((((False ∧ ((p3 ∧ (False → (p3 ∧ (True ∨ p4)))) → p1)) ∧ ((p2 → p1) → p4)) ∨ (p2 ∨ (p1 ∧ p1))) ∨ ((False ∧ p4) → p4))) := by
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
theorem thm_5_vars_216064007127635298880368876286 : ((p5 ∨ (p5 ∨ (False ∧ p5))) ∨ ((p3 → False) ∨ (((p1 ∧ p3) ∧ (((p2 ∨ (p1 ∧ False)) ∨ False) ∧ (p1 ∧ (True → False)))) ∨ (False → p5)))) := by
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
theorem thm_5_vars_263089531828830004116195264878 : (True ∧ (((((p1 ∧ (((p4 ∨ p3) ∨ p5) → (p5 ∧ ((p5 → (p4 → (True → False))) ∧ False)))) → (p3 ∧ p4)) → False) → p3) ∨ (p3 → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788161470573405706449390381530 : (((p5 ∨ (((((p3 → (p1 → p2)) ∧ p4) → p5) → (p4 ∨ ((p5 ∧ ((((p5 → p1) ∧ p1) ∧ False) ∨ (True ∧ p4))) ∧ False))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47171718095690157570492106169 : (((((((p2 ∧ (p4 ∨ p3)) ∨ (p5 ∧ p1)) ∨ True) → ((p1 ∧ False) ∨ True)) ∨ (((False ∧ (p1 → p1)) → p4) → p3)) ∨ (True ∧ False)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241369160863974111637926028583 : ((False → False) ∧ ((p1 → p5) ∨ (((((((p5 → (True → (p1 → p5))) → p4) → ((True → p4) ∨ p4)) ∧ p4) ∨ (p3 ∨ p1)) → p5) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130115289084557187622835585785 : ((((((p5 ∧ (p4 → ((p2 ∨ (False ∨ p4)) ∧ (True ∨ p2)))) ∧ (p1 ∧ p4)) → p3) → (p3 → p1)) ∨ (True ∨ False)) ∧ (p1 → (True ∨ p4))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147963306366716773885811867037 : (((p3 ∨ ((p5 → (False ∧ p5)) ∧ ((p1 ∨ p5) ∧ (p5 ∧ ((False ∨ p5) ∧ (False ∨ p3)))))) ∧ (p1 → False)) ∨ (p5 ∨ (True → (True ∨ False)))) := by
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
theorem thm_5_vars_343563639507335477478579327051 : (p2 → ((p4 ∨ p2) → (p1 ∨ ((p3 ∨ p4) ∨ (p5 ∨ (((True → p2) ∧ ((p5 ∨ (p5 ∨ (p5 ∧ (p2 ∨ p1)))) ∨ (p2 → p2))) ∨ p5)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_584632281835969912013979384 : (((((((p2 ∧ (p5 ∨ p1)) ∧ (True → p4)) ∨ p4) ∨ p4) ∧ (p1 → ((((p1 → True) ∧ p3) → p1) ∧ (p2 → p1)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671000183450828611534575371930 : ((((p5 ∧ (p5 ∨ (p5 ∨ ((p2 ∨ p4) → (p1 ∨ (p4 → ((True → (p5 ∧ (p4 → (p3 → p5)))) ∧ p3))))))) ∨ (p1 → (p5 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779997268787499100847959036349 : (((p2 ∨ (((False ∧ (((True ∧ (((p4 → (True ∨ p4)) ∨ p3) ∧ (False ∨ p5))) ∧ (p1 ∧ (p4 ∨ False))) ∨ p2)) ∨ p5) ∨ (True ∨ True))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_168983493449657698225984098214 : ((False → (p3 ∨ ((p3 → False) → (((p5 ∧ True) ∧ (p5 ∧ ((p5 ∧ p3) → p5))) ∧ p2)))) → ((((True ∧ p5) → p3) → p4) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58184411082574082723375915579 : (((p3 ∧ p3) ∧ (p2 ∧ ((((True → p1) ∨ False) → ((True ∧ p2) ∨ (((p1 ∧ p4) ∨ p3) → ((p1 ∧ p3) ∧ (False → False))))) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52766174843314607978074178421 : ((((True ∧ (p3 ∧ (p5 ∨ (((p1 → False) ∧ (p1 ∧ True)) ∨ p1)))) → p2) → ((p5 ∨ p2) ∨ (p5 ∧ ((p4 ∨ p4) ∨ (p1 ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306192417849157186429127708782 : (p1 ∨ ((p4 ∨ (p1 ∧ p3)) ∨ ((p2 → ((((((((p5 ∧ p2) → (p1 ∧ p4)) → p5) ∧ p5) → p2) ∧ (p1 ∨ True)) → p2) → p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169470215924344695982308389822 : (((((p4 ∨ False) ∨ (p2 → p2)) ∨ (p4 → (((p1 ∨ True) ∨ p2) → True))) ∨ False) ∧ (((p2 → p2) → ((True ∨ (p2 ∧ p2)) ∧ False)) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351518616846708097978238218394 : (p4 → (((p5 → ((p4 → False) ∧ (((p2 ∧ p4) → p5) ∧ ((p2 ∨ p2) → (p1 ∨ p5))))) ∧ p5) ∨ (p2 → ((p2 ∧ p3) ∨ (True ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76682973704600993286945860161 : (((((p1 ∨ False) ∨ (((True → (False ∧ p4)) ∧ (True ∧ p1)) ∧ ((p2 ∨ p1) → p5))) ∨ ((p3 ∧ ((p3 ∧ p4) → p2)) → p3)) → False) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ False) ∨ (((True → (False ∧ p4)) ∧ (True ∧ p1)) ∧ ((p2 ∨ p1) → p5))) ∨ ((p3 ∧ ((p3 ∧ p4) → p2)) → p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38103733279428052797841303989 : ((((p5 → (p3 ∧ (((((p2 ∧ p4) ∨ (p3 → p5)) ∧ (False → p2)) ∧ (p5 → p4)) ∨ (p1 ∨ (p1 → p5))))) → (True → p2)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66111458496588952393513817507 : ((p5 ∨ (((False ∧ p3) ∨ ((True → ((p1 ∧ (p4 ∧ ((p2 → (p2 ∨ True)) ∧ p4))) ∧ p2)) ∧ (p5 → (p4 ∨ (p4 → p4))))) → p1)) ∨ p4) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160545582733316142542041987205 : (((p1 ∨ ((False → (p1 → (p4 → (True ∧ p2)))) → (p1 ∧ False))) ∨ ((p3 ∧ (True ∨ False)) → False)) → ((p3 ∧ p5) ∨ ((p5 ∧ False) → p2))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590286459010579187873244161675 : ((((((p1 ∨ ((p5 ∧ p2) ∧ p1)) → (p1 → ((p5 → ((True ∧ p2) → (p1 ∨ (p5 ∨ True)))) → ((p5 ∨ True) → p1)))) → p3) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49180112805570516798779692277 : (((((True ∧ (p3 → p4)) → p4) ∨ ((((p5 → (p1 ∨ p2)) → p1) ∧ p3) ∨ (p5 → ((p4 ∧ p2) → False)))) ∨ (p4 ∨ (True → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351444342860291883808980152753 : (p4 → (((((p1 ∨ (p3 → ((p4 ∧ p3) ∨ True))) → ((p4 ∨ p2) ∧ (p4 → p4))) ∧ p1) ∧ (p1 ∧ p3)) → ((p2 → False) ∨ (False ∨ p1)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66812119658647497554649235328 : ((True → (p5 ∨ ((p2 → ((p1 ∨ ((p5 → (False ∧ p2)) ∨ (((p1 ∨ p4) ∧ ((p4 → p2) ∧ p1)) → False))) ∨ (True ∧ p5))) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40294616037277251829802688002 : ((((p5 → (((((p2 ∧ p1) ∨ (p2 ∧ ((p1 ∨ True) ∧ p3))) → False) ∧ (False → ((True ∧ False) ∧ p2))) ∧ (True → p2))) ∧ p1) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16582593809502174097023196712 : (((((False ∨ p5) ∧ ((p4 → ((p1 ∨ ((p1 ∨ p5) ∧ ((p3 ∨ (p2 → p2)) ∧ p4))) ∧ p1)) ∧ p3)) ∧ p5) ∨ (p3 → (p4 ∨ p3))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712102097673754855574054002609 : (((((p1 ∨ (p5 ∧ (p5 ∧ False))) ∨ p1) ∨ (p4 ∨ ((((p2 ∧ False) → p5) ∨ ((False → p4) → (p4 → False))) ∨ ((True ∧ p4) ∧ p5)))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205389276347148110096512486560 : ((((False ∧ p1) → True) → (p1 ∧ p2)) ∨ (((False ∨ p4) → p5) ∨ ((p1 ∨ True) ∧ (((p5 → False) ∨ (False ∨ (p3 ∨ p4))) → (p2 → True))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616963285380470162560490027229 : (((((p2 → (((p5 ∨ p4) ∧ (False ∨ p5)) ∧ (p4 ∧ p3))) → (((p4 → p4) ∧ (p4 → ((p2 ∧ p4) ∧ (True ∨ p2)))) → False)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_190356373708041347182942090315 : ((((False → (True → True)) → (p1 ∧ (p3 → p2))) ∨ p3) ∨ ((p2 ∨ (p1 ∧ (False → (False ∨ p5)))) → (False ∨ ((p1 → False) ∨ (p1 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325672883546816439572453419011 : (p5 ∨ (p1 ∨ (((((p4 ∧ (p1 ∨ ((((p5 ∧ (p4 ∨ p1)) ∨ p3) ∧ (p1 ∨ p3)) ∨ (True ∧ p1)))) → p1) ∧ p1) ∨ (False → p5)) ∨ p1))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110933476816913603613856799019 : (((((p4 → (((p3 ∧ ((p2 ∨ (True ∨ (p4 → p1))) ∨ (p4 ∨ p1))) → False) → (p1 ∧ True))) → p2) ∧ (p2 → True)) ∧ p4) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_23263011417727785477300097676 : (((p4 → (p1 ∧ ((p2 ∧ p2) → p2))) → (((p4 → (False ∨ ((((p5 → p1) → True) → True) ∨ ((False → False) ∨ p2)))) → p2) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263107268942169314760293149156 : (True ∧ (((p1 → (False ∨ ((True ∧ (False ∧ p3)) → (True ∨ (((((p1 → False) ∧ p2) → p5) ∧ p3) ∧ False))))) → (p2 ∨ p1)) ∨ (True ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307717903638127191879392984866 : (p1 ∨ (p2 → (p3 → (((((p2 ∨ p5) → p5) ∧ p1) → (False ∨ (p1 → p4))) ∨ (True → ((((p3 → p3) ∧ p1) ∧ (False ∨ p3)) ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777839770784722423045053149630 : (((p1 ∨ ((((False ∨ p4) → p1) → p4) ∨ (p4 ∨ (p1 ∨ (p1 ∧ (((p2 → (False ∧ p1)) ∧ p1) ∨ (p1 → (p4 ∧ (p5 ∧ False))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185198815571397770981792272300 : ((True ∧ ((p5 ∧ ((p4 ∨ True) ∧ p5)) ∧ (p1 ∧ (p5 ∨ p2)))) ∨ ((((True ∨ (False ∧ (True → False))) ∨ True) → (False → False)) ∨ (p3 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157993817459088321060874445603 : ((((p4 → (p3 ∨ p2)) → (False ∨ (p5 → p4))) → (((((p4 ∧ False) → p2) ∨ p5) → p5) ∨ True)) ∨ (p2 ∧ ((True → p2) → (p5 ∨ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205305246931574539722697907215 : (((False ∨ (p1 ∨ p2)) ∨ (p5 ∧ p5)) ∨ ((p5 ∨ (p1 ∧ ((p4 ∧ ((p5 → p4) → (p3 ∨ (p4 ∧ p4)))) ∨ (p3 ∨ p1)))) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106158430843401993129557046207 : (((p1 ∨ (((((False ∨ p3) → False) ∨ p2) → True) ∧ (p5 ∧ True))) ∨ ((p4 ∨ (p2 ∧ (p2 → False))) ∨ (p5 → (p1 → p5)))) ∧ (True ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



