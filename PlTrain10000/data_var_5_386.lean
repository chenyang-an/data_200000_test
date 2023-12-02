variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232713221106750273328248945669 : ((p1 ∧ (p3 ∨ p5)) → (((((p3 → (p2 ∨ ((p2 → p4) ∧ p2))) → ((p2 → p3) ∨ p2)) ∧ p1) ∧ p2) ∨ (p1 ∨ (p3 → (p1 ∨ p1))))) := by
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
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245993764941991859026250905511 : ((p4 ∧ True) ∨ (p1 ∨ ((((p4 → (False → p3)) → ((p2 ∧ ((p1 → True) → p3)) → p4)) ∨ (p3 → ((False ∧ p4) → (p5 → p1)))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62063016809602088068806266627 : ((p2 ∧ (True ∧ ((((p4 → p5) ∧ (((False ∧ ((p5 → p1) → ((p1 ∧ p2) ∧ p2))) ∧ p1) ∨ (p3 ∧ False))) ∧ (p3 ∧ p4)) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138007117126518423743921580234 : ((True → (((p3 ∧ ((p5 ∧ (((((p1 → p5) ∧ p4) ∧ (True ∨ p3)) ∧ True) → (p4 → False))) → p4)) ∧ True) ∧ p5)) ∨ ((False ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150181321179814468442439338220 : ((p1 → (True → ((((((False → p1) → (p3 ∧ p3)) ∧ (True ∧ p5)) ∧ (p2 ∧ p5)) ∧ (p2 → False)) ∨ True))) ∨ ((False ∧ (p5 ∨ p3)) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183800758427230861232050143972 : (((((p3 ∨ (p1 ∧ p4)) ∧ ((p2 ∨ False) → p4)) ∨ p4) ∧ False) ∨ ((p3 ∧ (True ∨ (p1 ∧ p2))) ∨ (p3 ∨ (p2 → ((True ∧ p1) ∨ p2))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25582206083506202876901363789 : (((False → (p3 → True)) → (((p2 ∨ (False → p1)) → ((p2 ∧ True) ∨ (((p4 ∨ (True ∧ False)) → p2) → (False ∨ False)))) ∨ (p5 → p5))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218523808057892296629413487814 : (((p4 ∨ True) → (False ∨ False)) → (True → ((((p2 → (((((p4 → True) ∧ (p3 → p3)) → True) → p1) ∧ False)) ∨ (p4 → p1)) ∧ p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643306516002099600563724090027 : ((((p3 ∧ (p3 ∧ (((((p3 ∧ p2) ∨ (p2 ∨ (p3 ∨ p3))) ∧ True) ∧ (p1 ∧ p5)) → (p2 ∨ ((p5 → p3) ∧ (p3 → p2)))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165932238722231397147427861697 : (((p4 ∧ p5) ∧ (p1 → ((p5 ∧ ((p5 ∨ (p2 ∨ (p3 ∨ p5))) ∨ (p3 ∧ False))) ∧ p1))) ∨ ((p1 ∧ ((p2 → (p5 ∧ p3)) ∧ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340793536186162457292830864502 : (p2 → ((((True ∧ False) ∨ ((p3 ∧ (((False → (((True → p5) → ((p2 ∨ p2) → p5)) → (p3 → True))) ∧ True) → p1)) → True)) → p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619621938614402392962514771326 : (((((p2 ∧ False) ∧ (((((p1 → p3) ∧ p2) ∧ p4) ∨ True) ∧ ((p3 → (p5 → (p1 ∨ p3))) → ((p2 ∨ True) ∧ (False → False))))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_745020571276705067610724422321 : ((((p4 ∧ p1) → ((True → False) ∨ ((False → False) → ((p2 ∨ (True ∧ (p5 ∨ (((p4 → p3) ∧ (p3 → p4)) ∧ (True ∧ p4))))) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255161385502144357542700842606 : ((p4 ∧ p3) → (p4 ∧ (p2 ∨ ((((((((p4 ∨ (p5 ∨ p1)) → p1) ∧ True) → p3) → (p4 ∧ p2)) ∨ p4) ∨ (p4 ∨ (p5 ∨ True))) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65951519686892554307091225348 : ((p4 ∨ (p3 ∨ ((((p1 ∧ p5) ∨ p5) ∧ ((True ∧ p5) → (True → (((p1 ∨ p5) → False) ∨ (((False ∨ p2) ∧ p4) ∧ p3))))) → p2))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (True ∧ p5) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : (p1 ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h20
  case inr h21 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h22 : (True ∧ p5) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h21
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h23 := h3 h22
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h24 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h25 := h23 h24
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
      have h27 : (p1 ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h26, we can now drive its conclusion.
      let h28 := h26 h27
      -- False on the left can always be used.
      apply False.elim h28
    case inr h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- Conjunctions on the left can always be decomposed.
      let h32 := h30.left
      let h33 := h30.right
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h34 =>
        -- False on the left can always be used.
        apply False.elim h34
      case inr h35 =>
        -- One of the premise coincides with the conclusion.
        exact h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137952135014110799626243588149 : ((p5 ∨ ((p2 ∨ (p5 ∨ (((p4 → (((True ∨ False) ∨ (p4 ∧ p3)) ∨ (p1 ∨ p4))) ∨ (p4 → True)) → p5))) ∨ True)) ∨ (p4 → (p1 → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621959810934387441193398607810 : ((((p1 ∧ (p5 ∨ (p5 ∨ ((((p4 → (True ∨ True)) ∧ (p5 → (False ∨ p3))) → ((False → (p1 → False)) → p3)) ∧ (p1 ∨ p3))))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_112260167447027419149067742781 : (((p4 ∨ (p1 → ((((p2 ∧ (p5 → p5)) → p2) ∧ (((p1 → (True ∨ True)) → (p4 → p2)) ∧ (p3 ∨ False))) → p4))) ∨ p5) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806377667426285736766033993405 : (((p4 → ((p3 ∨ ((False ∧ (((((p1 → (True → ((p3 ∧ ((p2 ∨ p2) → p2)) ∨ p4))) ∨ p4) ∨ False) → p1) ∨ p1)) ∨ p4)) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_165852882231016528706595133417 : ((((p5 → p2) → p3) ∨ (p1 ∧ (((p1 ∧ p5) ∧ (p4 ∨ ((p1 ∧ True) ∧ p1))) → p1))) ∨ (((p5 ∨ (p2 → (p5 → p1))) ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163014556586448004852402196125 : (((((p4 ∧ True) ∧ (((False ∨ p4) ∨ p4) ∨ (p4 ∧ p1))) ∨ p2) ∨ ((p1 → p1) → True)) ∧ (False → ((False ∨ ((p5 → p4) ∧ p3)) ∧ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52532844003215044169891328995 : (((((p4 → (p2 → False)) → ((p2 ∧ ((p2 ∨ p3) ∧ p3)) ∧ True)) ∨ p2) ∨ (((((p1 → p3) ∨ p1) → p1) ∧ (True → False)) → p3)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42983109099290693937808477208 : (((p5 → ((True ∨ (p2 → p5)) → ((True ∧ ((((p2 ∧ (True ∨ False)) ∨ p3) → p5) → p3)) → (p3 ∧ ((True ∧ p4) → p2))))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328421028584107578835762239412 : (True → ((((p5 → p1) ∨ (p1 ∨ p4)) → (((p5 ∨ ((p4 → (p2 ∨ p5)) → p4)) → p2) ∧ False)) ∨ (p5 → (True ∨ (p3 ∧ (True ∨ p1)))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50690875555022811698985522134 : ((((True → (p1 ∨ True)) ∧ ((p4 ∧ (p1 ∧ p5)) ∧ (p1 ∨ ((p4 → (p5 ∧ p5)) ∨ (p1 → False))))) → ((p2 ∨ (False ∨ False)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47173002439932959354551838911 : (((((p5 → (True → p5)) → (((p1 → p4) ∨ (p4 → (p1 → p5))) → p3)) ∨ ((p4 ∧ p1) → ((p4 ∧ True) ∨ p5))) ∨ (True ∨ p4)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190468104482029298964832270216 : (((((p2 ∧ (p3 ∨ (p3 ∧ p3))) → False) ∧ p1) → False) ∨ (((((p3 ∧ p3) ∨ (False ∧ (False → p4))) ∨ True) ∧ True) ∨ ((p2 → True) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_567119393222718054836052431146 : (((True → (p5 ∨ ((((p2 ∨ (p3 → p5)) ∧ (p5 ∧ (((((False → p3) ∨ (True ∨ False)) ∨ p4) → p4) ∨ (True → p3)))) ∧ p5) ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_87279994954994166249344129190 : (((((p4 ∧ (p5 ∧ p2)) → p5) → False) ∧ (False → (p4 ∨ ((((p5 ∨ ((True → (p1 ∧ p5)) ∨ p5)) → (False ∧ p4)) ∨ p5) ∧ True)))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 ∧ (p5 ∧ p2)) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h4
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39535788181851581282872951042 : (((False ∨ ((p3 ∨ p5) ∧ ((p1 ∨ (((p4 ∨ p3) ∨ p5) → p4)) ∧ (p1 ∧ ((((p3 ∨ False) → (p2 ∨ False)) ∨ p1) → False))))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788421901139255388791614401069 : (((p5 ∨ ((((p5 → True) → (((p3 ∧ p4) ∧ p4) ∧ (p4 → p4))) ∨ (True → ((((p1 ∧ p5) ∧ p3) ∨ True) ∨ (False ∨ p2)))) ∨ p1)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782344676893943198414468455555 : (((p3 ∨ ((((((False → p2) ∧ ((p4 ∧ (p4 ∨ p5)) → p5)) ∨ p1) ∨ ((p5 ∨ p5) ∨ (((p5 ∨ p3) → p2) ∨ True))) ∧ True) ∨ p4)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217647614492096896730211176106 : ((((True ∨ p3) → p3) → p4) → ((((p2 ∧ (p3 → (p1 ∨ (False ∨ p1)))) → p1) → p4) ∨ (((p5 ∧ ((True → p2) → p4)) → p5) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250044004890272997795423386262 : ((True → p3) ∨ ((p1 ∨ ((p1 ∧ (True ∧ (p3 ∨ p4))) → p2)) ∨ ((p4 ∧ p3) → ((True ∨ (p1 ∨ True)) → (p5 ∨ (p4 ∨ (p5 → p5))))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h1.left
      let h12 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114390648063800686120003672031 : ((((True → (p1 ∧ (True ∨ ((True ∨ p1) ∨ ((p4 ∧ (p4 → p5)) ∧ p4))))) → (p1 → p2)) ∨ ((p3 → p1) ∨ (p3 → True))) ∨ (p1 ∧ p1)) := by
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
theorem thm_5_vars_251190780232324695067287634330 : ((p2 → p1) ∨ ((p3 ∧ (((p3 ∨ (p5 ∧ (p1 ∧ (p3 ∧ (p5 ∨ (p5 ∨ p2)))))) → (p5 ∧ False)) → False)) ∨ ((p1 ∧ (p2 → False)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337755497399791361731646390937 : (p1 → (((p2 ∧ (p3 ∧ ((p4 ∧ p3) ∨ (((p3 ∨ p1) ∧ (p5 → p5)) → p2)))) ∧ p4) ∨ (((p4 ∨ False) ∨ False) ∨ ((p3 ∧ p4) ∨ p1)))) := by
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
theorem thm_5_vars_134389549449186191935282214688 : (((p5 ∨ ((p4 → (p3 → (False ∧ p1))) → (((p1 ∧ (p2 ∧ p1)) → ((False → False) ∧ False)) ∨ (p5 ∧ p3)))) ∨ True) ∨ ((p2 ∨ p1) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64329696257718131645743050496 : ((p1 ∨ ((((p4 → p5) → False) ∧ ((p2 ∨ ((((p3 ∧ p1) ∧ p4) ∧ (False → (p3 → (p3 → p2)))) → True)) ∨ (p4 ∨ p3))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39253209694246898200752780200 : (((False ∧ (((p1 ∨ (True ∧ p2)) → (p4 → ((p5 ∧ (p5 → p4)) ∧ p4))) ∨ ((p4 ∨ (p3 ∨ (True ∨ (p4 ∧ p1)))) → p2))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663841044855177835016809733631 : ((((p3 ∧ ((((p3 ∨ (p2 ∨ (True ∧ p4))) ∧ (p5 ∧ p2)) → (True ∧ (p3 ∧ (False ∨ (p4 ∨ (p5 ∨ True)))))) → True)) → (True → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803673348813984584363050355950 : (((p3 → ((p2 ∨ ((((False ∧ ((False → (False ∧ False)) → p2)) ∨ p4) → (True ∧ ((p4 → (p1 ∨ p5)) ∨ (p1 ∧ p3)))) ∧ p4)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191921321076282715393670554374 : ((True → ((((p3 ∧ p2) ∧ (True ∧ True)) ∨ p3) ∧ p1)) ∨ (p1 → (False ∨ (((p5 ∨ False) ∧ ((False ∨ p1) → ((p3 ∧ p2) ∧ False))) ∨ True)))) := by
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
theorem thm_5_vars_600069569968285687525078603437 : (((((p2 ∨ p5) → ((p4 ∧ (p4 ∧ (((p3 ∧ p3) ∧ p5) ∨ (p4 ∨ (True → (False ∨ (p5 ∨ p2))))))) ∧ (p2 ∨ (p2 ∨ p5)))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233321787359984917418826224918 : ((True ∨ (False → True)) → (p5 → ((False ∧ p3) ∨ (((p2 ∨ p4) ∨ (((False → p2) ∧ True) ∧ (p4 → (p5 ∨ ((False ∨ p2) → True))))) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135106295738872389282669457345 : (((((p4 ∨ p4) ∨ p4) ∧ (p3 ∧ (((p3 → p2) ∨ (p5 → p1)) ∨ ((True ∧ (p3 ∨ True)) ∨ True)))) ∨ (False → p3)) ∨ (True ∧ (p1 ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40727233376243485455175855735 : (((((p5 ∧ ((p3 ∧ True) ∧ (True → p4))) → (((p2 ∧ p5) → p5) ∧ ((p1 ∧ (True → ((True → p2) ∨ True))) → p4))) → p3) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807478332540605566649287706577 : (((p4 → ((False → ((((p5 ∧ True) ∨ p2) ∧ p5) ∧ p3)) → (False ∧ (((False → ((p1 → (p3 ∧ True)) ∧ False)) → p3) ∨ (p5 → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41443291258356437368386925893 : ((((p2 ∨ (p4 ∧ (((p1 → p5) ∨ p2) ∨ (((p5 ∧ True) ∧ False) ∨ p1)))) → (((True ∨ p4) → p3) ∨ ((False → p3) ∧ p4))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64219337097482634927748512470 : ((False ∨ (p4 ∧ ((p4 → (False → (p1 ∧ p4))) → (p1 → (p2 ∨ (((False → (p1 ∨ p5)) ∨ (p4 → (False ∨ (p2 ∨ p5)))) → p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115146669825263725516334606686 : (((True ∨ (((False ∧ ((False ∧ (p3 ∧ p2)) ∨ p2)) ∨ p4) ∨ p3)) → (((p3 ∨ p3) ∧ (p2 ∧ p1)) ∨ (False → (p1 ∧ p4)))) ∨ (False ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- False on the left can always be used.
        apply False.elim h7
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h10
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h12
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749088338067013130490347952664 : ((((p5 → False) → ((((p3 ∨ p4) ∨ ((((False → True) → (True ∧ p4)) → (True ∨ ((p2 → p3) ∧ False))) → True)) ∧ (p3 ∧ p1)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43705416297209575951148464246 : (((((True ∧ ((p2 ∧ p2) ∨ False)) ∧ ((((p2 ∧ (p1 ∨ (((p5 ∧ False) ∨ p4) ∧ p3))) ∧ True) → p5) ∧ (False → p2))) → p5) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726312134002259878460800819364 : (((((p3 ∨ False) ∨ p1) ∨ (((((((p4 → (p4 ∧ (p1 → p2))) ∧ (False ∧ p1)) → p3) → p2) → p3) → (p4 ∧ p5)) → (p1 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165232154398797436197793348143 : ((((p3 ∧ p4) ∨ ((True ∨ ((p4 → p5) ∨ False)) → (p4 ∧ (p5 → p4)))) ∨ (p4 ∨ True)) ∨ (p4 → (p3 ∧ (p5 ∨ (p4 ∨ (p2 ∧ p4)))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264229077997526321084545632835 : (True ∧ (((p1 ∨ (p3 → p3)) ∧ (True → True)) ∧ ((False ∨ p3) ∨ ((p5 → (p5 ∨ (p4 ∨ p1))) ∧ ((p2 → False) ∨ (p3 → (p1 ∨ True))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55634647696187169680179474540 : (((((p4 ∨ p1) ∧ p2) ∧ p2) ∧ ((((((True → p5) → ((p1 → p5) → p1)) ∨ (p5 ∨ p5)) → False) ∨ (p1 ∨ (p1 → p3))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780400240162912202862218039479 : (((p2 ∨ (((p3 → (p3 → (((p3 ∨ p5) ∨ p1) → p2))) ∨ (p2 ∨ ((p4 → True) ∧ True))) ∨ ((p4 → ((False ∨ p2) ∧ False)) ∨ p1))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680115519186201011646958038597 : (((((((p3 ∨ (p2 → (False ∧ (True ∨ p2)))) ∧ p4) ∧ (True → ((p2 → p2) ∧ p4))) ∧ (p2 → p5)) → ((False ∨ (p3 → p5)) ∨ True)) ∨ p1) ∧ True) := by
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
  cases h6
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660091841924495048885454504706 : ((((((p4 ∨ (((p2 ∧ p5) → ((p1 ∨ True) ∨ p1)) ∨ (((p1 ∧ p2) ∧ False) ∨ p3))) ∧ (p1 ∧ (p1 ∨ p3))) ∨ p3) → (p2 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228967211808776957699928063788 : ((p4 ∨ (p2 → p4)) ∨ (((False ∧ False) ∨ ((p2 ∧ (((p4 ∧ ((p3 ∨ (True → (p1 → (p2 ∨ True)))) → True)) ∧ p4) → True)) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722051675856208336340013037957 : ((((p1 → (p2 ∧ (False → False))) → ((((p5 ∧ (False → (p1 → (p5 → p1)))) → ((((p3 ∨ p5) ∧ p4) ∧ p5) ∨ True)) → p3) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257266753328193895637237946129 : ((p2 ∨ p3) → ((((((p2 → p2) → p1) ∨ p4) → True) → (False ∧ (True → (False ∨ p5)))) ∨ (p5 → (p1 ∨ (p1 → (p1 ∨ (p1 ∧ True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62507958308046241762686431069 : ((p3 ∧ (p2 ∧ ((p5 ∧ True) ∧ ((p4 ∧ p5) ∧ ((p5 ∨ (False ∧ (True → (p5 → p4)))) ∧ ((False → (False ∧ (p3 → False))) ∧ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120378611948436272870065869504 : (((True → (((p4 ∨ ((p2 ∧ p3) ∨ p4)) → True) → (((p3 → p4) → (((p5 ∨ (p2 ∧ p4)) ∧ True) ∨ p2)) ∧ False))) ∧ p5) → (False ∨ p2)) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((p4 ∨ ((p2 ∧ p3) ∨ p4)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324211728687092102107419125636 : (p5 ∨ ((p2 ∨ ((((True ∧ True) ∧ p1) ∨ (p5 → p3)) ∨ p1)) → (((p2 ∨ p4) ∨ p5) ∨ (((p3 ∨ (p2 → True)) ∧ (False ∨ p4)) ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319545460170205456458311724510 : (p4 ∨ (((((False ∨ False) ∨ (True ∨ True)) ∨ p3) → (False ∨ p5)) ∨ (p3 ∨ (((p2 ∧ (p4 ∧ True)) ∧ ((p1 ∨ (False → p2)) ∧ False)) → False)))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342397138326347340654024013128 : (p2 → (((p5 → p4) ∧ (((p3 ∧ (True ∨ (p5 ∨ p4))) ∨ (p4 → p1)) → (True → p3))) ∨ ((False ∨ ((False ∨ p3) ∧ p5)) ∨ (p2 ∨ False)))) := by
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
theorem thm_5_vars_118724197093673711557896213139 : ((p5 ∨ ((p4 ∨ (p3 → (p3 ∧ ((p3 → (False → True)) ∧ (((False ∧ p3) ∨ (True → p4)) ∨ False))))) ∨ ((p2 ∧ p5) ∨ p4))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352021781836570215413877876992 : (p4 → ((((True → p3) ∧ ((p5 ∨ p5) ∨ False)) ∧ p4) → (((False ∨ (((((True ∨ True) ∧ False) ∧ False) → True) ∨ p2)) → (p3 → p1)) ∨ p4))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353717144970108805930156142629 : (p4 → (True → ((True ∧ ((((p4 → False) ∨ (((p5 ∧ False) ∧ (p5 → ((p1 ∧ p5) ∧ (p3 ∨ p2)))) ∧ (p5 ∧ True))) ∧ p5) ∨ p4)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138402837198172465452084642187 : ((p4 → (p5 → ((p1 ∨ ((((p1 ∧ p1) ∧ (((p3 → p3) ∨ True) → (p5 → True))) ∧ p3) ∧ p3)) ∨ (True ∧ p4)))) ∨ ((p1 → p5) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206244242126897129778142740290 : ((False ∨ (((p1 → True) → p1) ∧ p3)) ∨ ((p5 ∨ True) ∨ ((p4 ∨ p2) → (p1 → (((((p4 ∨ False) → True) ∨ (p4 → p4)) ∨ False) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56523257437158020613142076704 : (((p5 ∧ (p5 ∨ (p5 → p5))) → (p1 → ((((((p2 ∨ (False → (p2 ∨ True))) → p2) ∧ p2) ∧ ((p5 ∨ p3) ∨ p3)) ∨ p4) ∨ p5))) ∨ False) := by
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
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219875715028526518017628699120 : ((p3 → (p4 → (True ∧ p4))) → ((((p4 ∧ p2) → (((((True → p1) ∨ p1) → (False ∨ (False ∧ p3))) ∧ (p5 ∧ p4)) ∨ p1)) ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68371769334965223469631077691 : ((p3 → ((((p5 ∧ False) → p5) ∨ (False ∧ p4)) → ((((p3 → (p3 ∨ p4)) → p3) ∧ p1) ∧ (False ∧ (((True ∧ False) → True) → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190431791820901695107045360656 : (((p5 ∨ ((((p5 ∨ p5) → p1) → p5) ∨ p3)) ∨ p3) ∨ ((((False ∨ p5) ∨ (p4 ∨ (((p4 ∨ (True ∧ True)) → False) ∧ False))) → True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159192763678847867011653439546 : ((p2 → (((((p4 ∨ (p4 → (p5 → ((p2 → p4) ∧ p4)))) ∧ (p2 ∧ p2)) ∧ p5) ∧ p1) ∨ p3)) ∨ (p4 ∨ ((True ∨ (p2 ∨ p1)) ∨ p2))) := by
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
theorem thm_5_vars_731558416302297474900371825911 : ((((False → (False → p1)) → (((False → p5) ∧ p1) ∨ ((p3 → ((p2 ∨ p3) ∨ (p5 → True))) ∧ ((p1 ∧ (p4 ∨ False)) → (p5 ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246211646599191018889104680586 : ((p4 ∧ p3) ∨ ((p3 ∨ ((p4 ∨ True) ∧ (True → (((p1 ∨ (p2 → (False ∨ (p4 → False)))) → p4) ∨ p5)))) → (p3 ∨ ((p5 ∨ p3) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
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
theorem thm_5_vars_303220492990640346028139642927 : (False ∨ (p5 → (((p2 ∧ (p3 ∧ (p2 ∧ (((p1 ∨ p2) → False) ∨ ((p2 ∧ p1) → (True ∨ (p5 ∧ False))))))) ∨ (p3 → (p3 ∨ p1))) ∧ p5))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684232855919150413921479831236 : (((((p2 ∨ (((True ∨ (True ∧ p2)) ∧ False) → ((p4 → (p3 ∧ True)) ∨ p4))) → (False ∧ p1)) ∨ (p5 ∨ (((p4 ∨ False) → p1) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56641086381853765295991038776 : ((((False ∨ True) ∧ p1) ∧ ((((False ∧ p2) → (p2 ∨ p3)) ∧ (True → p5)) ∨ ((True ∨ ((True ∨ ((p3 ∧ p4) ∧ True)) ∨ p2)) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55550334073374718659505693062 : (((p2 ∧ (((p3 ∨ p4) ∧ p1) ∧ p5)) → ((((True ∧ ((p1 → p1) ∧ ((p3 ∨ (p5 → False)) ∨ True))) → p4) ∨ (False ∧ p4)) ∨ p1)) ∨ p2) := by
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
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689222075874340188496429861741 : ((((((p3 ∨ p5) ∨ (((p3 → False) → (True ∨ True)) ∧ ((p3 ∨ False) → p3))) → False) ∨ (((False ∧ ((p3 ∧ False) ∧ p5)) ∨ p5) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137317676145737051361635024906 : ((p2 ∧ (((False ∨ (p1 ∧ p4)) ∨ p4) → ((p3 → p2) ∨ (p3 ∨ (((p2 ∧ (p4 ∧ True)) ∧ (False → False)) ∧ p1))))) ∨ (True → (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42117533339492491335538766626 : ((((p5 ∧ p2) → ((p3 → (p5 ∧ (((p2 ∨ (False ∨ True)) ∧ p3) → (p4 ∨ (p2 → p1))))) → ((p5 → (True ∧ p3)) → p3))) ∨ False) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160688769748393178734307070839 : ((((p1 ∨ p5) → ((True ∨ p4) → (False ∨ False))) ∧ (False ∨ (p5 ∨ ((p3 → (p5 → False)) ∧ p5)))) → (((False ∨ p2) ∧ True) ∧ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h7 : (p1 ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h7
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : (True ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h10 := h8 h9
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h16 : (p1 ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h16
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h18 : (True ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h19 := h17 h18
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- False on the left can always be used.
        apply False.elim h21
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h22
  -- False on the left can always be used.
  apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50721005815402833468647141849 : ((((False ∧ p2) → (p3 ∧ (p4 → (((p3 ∨ p5) → False) → ((True ∨ (p2 ∨ False)) ∧ (p5 → p1)))))) → (p4 ∨ ((False ∨ p1) ∨ True))) ∨ p5) := by
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
theorem thm_5_vars_66243536383658424553603232824 : ((p5 ∨ ((False ∧ (p3 → ((p5 ∧ p5) → p1))) ∨ (((p4 ∨ p3) → ((p3 ∧ False) ∨ ((False ∧ (p3 ∧ (True ∧ False))) → p5))) ∨ p5))) ∨ p4) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316851663846930806363677588121 : (p3 ∨ (p1 → (((p1 ∨ ((p4 → ((p5 → False) → (p2 → p4))) → ((p1 ∧ (p5 → p3)) ∨ ((p5 → p2) ∨ (False → p2))))) → False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185844767886654534477081470208 : (((((True ∨ (p1 ∨ ((p4 ∨ True) ∨ p2))) → p5) ∨ p4) ∧ p3) → ((p4 ∧ p1) ∨ (False ∨ (p3 ∨ (False ∨ (((p2 ∨ p1) ∨ p4) ∧ True)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42987314511988464424142715020 : (((p5 → (False ∧ (True ∧ (((p2 ∧ ((True ∧ p3) → p4)) → p1) ∧ (((False ∧ True) ∨ (((p1 ∧ p4) ∧ p3) ∧ p5)) ∧ True))))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158337219472032289725354448032 : (((p1 ∧ p5) ∧ (p1 ∧ ((p4 ∨ False) → (p2 → ((p5 ∨ False) → ((p3 ∧ p2) ∨ (False ∧ p5))))))) ∨ (p3 ∨ (((False → p4) → True) ∧ True))) := by
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
theorem thm_5_vars_305517032209844834965463975811 : (p1 ∨ (((((p3 → ((p4 → (p5 ∧ p1)) → (True ∨ True))) ∧ p3) ∨ p5) ∧ p3) → ((p1 ∧ p2) ∨ (p5 → (((p3 ∨ p5) → True) ∧ True))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219594853988031972981793918777 : ((True → (False ∨ (p5 ∨ p3))) → ((True → (p1 ∨ False)) → ((True ∨ ((p1 → p5) → (p1 ∨ p1))) ∧ (((p4 → (p5 ∨ p2)) ∧ p2) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116740851612292738688182599879 : (((p4 ∧ p2) ∨ ((((p5 ∨ (((True ∨ (p5 → (True → p5))) → (p4 ∨ p1)) ∨ p2)) ∨ p1) → p1) ∨ (True ∨ (False → p5)))) ∨ (p3 ∨ p2)) := by
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
theorem thm_5_vars_355550691444666987369547451353 : (p5 → (((((p2 ∨ ((False ∧ p1) ∨ p4)) ∨ (((((p4 ∧ ((p2 ∧ True) ∧ p2)) → p5) → p5) → p1) → p3)) → p2) → False) ∨ (p4 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157655952035839455403471656086 : ((((p3 ∧ (((p1 ∧ False) ∨ ((p2 → p1) ∧ (False ∧ p2))) ∨ p1)) ∨ p3) ∨ ((p3 ∨ True) ∨ False)) ∨ ((p3 ∨ p2) → (p4 → (p2 ∧ p3)))) := by
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
theorem thm_5_vars_64258058582026481096002715266 : ((False ∨ (p4 ∨ ((((p1 ∨ p2) ∨ (p4 ∧ (((True → p2) → p5) ∧ p5))) ∨ False) → ((p4 → p3) ∧ ((p5 → (p3 → False)) → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



